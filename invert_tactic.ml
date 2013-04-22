open Invertlib

module Subst = struct

  type name =
  | Var of Names.Id.t
  | Rel of int

  let eq_name = (=)

  type t = (name * Term.constr) list

  let pp_name = let open Print in
		function
		| Rel i -> string "@" ^^ int i
		| Var v -> id v

  let pp_t (s:t) =
    let open Print in
    separate_map semi (fun (n,c) -> group (pp_name n ^/^ colon ^/^ constr c))  s

  let lift_name n = function
    | Var name -> Var name
    | Rel i -> Rel (i + n)

  let rec lift n = function
    | [] -> []
    | (Var name, t) :: q -> (Var name, Term.lift n t) :: lift n q
    | (Rel i, t) :: q -> (Rel (i + n), Term.lift n t) :: lift n q

  let rec apply subst term = match subst with
    | [] -> term
    | (Var name, t) :: q -> apply q (Term.replace_vars [name,t] term)
    | (Rel i, t) :: q-> apply q (Termops.replace_term (Term.mkRel i) t term)

  let apply subst term =
    let result = apply subst term in
    Print.(let doc = messages ["term", constr term; "result", constr result; "susbt", pp_t subst] in
  	   let doc = prefix 2 2 (string "apply") doc in
  	   eprint doc);
    result
end

type split_tree =
  ((Names.inductive * int (* constructor number *) *
      Term.constr list (* params *) * 'a list) option as 'a)

type split_tree_leaf =
  | LVar of Names.identifier
  | LRel of int
  | LTerm of Term.constr

(** [make_a_pattern env sigma t] decomposes the term [t] in a
   split_tree (the constructor spine that underlies this term), and
   the leaves of this split_tree (either variables or terms).

   [make_a_pattern env sigma (I params (C_i (C_j x) u))]
   @returns [[(Some (i, [Some (j, [None]); None]), [Inl x; Inr u])]]

   The left part of the result corresponds to the spine of the term
   [t], and the right part corresponds to the arguments of this
   spine. Note that the spine is actually a list of split trees, since
   the inductive may have several arguments.

    Params of constructors are putted in split trees because they are need to
    construct correct typing env for building diag.

    Note: the split_tree_leaf list corresponds to a telescope: that
    is, the most recent binder is a the end of the list.
*)
let make_a_pattern env sigma (args: Term.constr list) : split_tree list * split_tree_leaf list =
  let rec aux t vars =
    let (hd,tl) = Reductionops.whd_betadeltaiota_stack env sigma t in
    match Term.kind_of_term hd with
    | Term.Var v when CList.is_empty tl -> (None, (LVar v) :: vars)
    | Term.Rel i when CList.is_empty tl -> (None, (LRel i) :: vars)
    | Term.Construct (ind, i) ->
      let params,real_args = CList.chop (Inductiveops.inductive_nparams ind) tl in
      let (constrs,leafs) =
	CList.fold_map' aux real_args vars in
      (Some (ind, i, params, constrs), leafs)
    | _ -> (None, (LTerm t) :: vars)
  in
    let (a, b) = CList.fold_map' aux args [] in
    (a, b)

let make_a_pattern env sigma args =
  try make_a_pattern env sigma args
  with Not_found -> assert false

(** From the split_tree_leave list, we build an identifier list by generating
    variables y_s for the LTerm t_s.

    We must be able to substitute the t_s in the goal by the y_s: concl' =
    goal[y_s/t_s] must be typable.

    We must also generalize hypotheses not present in split_tree_leave that depends
    on an element of split_tree_leave to get the real conclusion
*)
let prepare_conclusion_type gl leaves =
  let vars = List.map (function LVar x -> Subst.Var x | LRel x -> Subst.Rel x) leaves in
  let concl = Tacmach.pf_concl gl in
  (vars,
   [||],
   concl)

let devil =
  Term.mkProd
    (Names.Anonymous,
     Util.delayed_force Coqlib.build_coq_False,
     Util.delayed_force Coqlib.build_coq_True)

let false_rect =
  lazy (Coqlib.coq_constant "Invert" ["Init"; "Logic"] "False_rect")


(* Given an inductive I, and a constructor C, build the match that
   filters the constructor C, and calls the [kt] function to build a
   term; otherwise, calls the [kf] function. *)
let mk_matchi env sigma ind constructor params term return_clause kt kf =
  let case_info = Inductiveops.make_case_info env ind Term.RegularStyle in
  (* the type of each constructor *)
  let (branches_type: Term.types array) = Inductiveops.arities_of_constructors env ind in
  let branches =
    Array.mapi
      (fun i ty ->
	let ty_with_concrete_params = Term.prod_applist ty params in
	let (args_ty,concl_ty) = Term.decompose_prod_assum ty_with_concrete_params in
	let branch_body =
	  if i + 1 = constructor
	  then
	    kt (Term.mkConstruct (ind,i + 1)) args_ty
	  else
	    kf (Term.mkConstruct (ind,i + 1)) args_ty
 	in
	branch_body
      )
      branches_type
  in
  let t = Term.mkCase (case_info,return_clause,term,branches) in
  t

let rec print_split_tree t =
  let open Print in
  match t with
    | None -> string "#"
    | Some (ind, constructor, params, split_trees) ->
      group
	(constr (Term.mkConstruct (ind, constructor))
	 ^^
	   (surround_separate_map 2 1 (break 1) (break 1 ^^ lbrace) comma (rbrace ^^ break 1) constr params)
	 ^^
	   brackets (separate_map comma print_split_tree split_trees)
	)

let print_split_tree_list (st: split_tree list) =
  let open Print in
  surround_separate_map 2 1
    (brackets empty)
    lbracket
    (semi ^^ break 1)
    rbracket
    (print_split_tree)
    st

let rev_append ctx stt =
  let result =
    List.rev_append ctx stt
  in
  Print.(eprint (
    prefix 2 2 (string "rev_append")
      (messages [
	"ctx", rel_context ctx;
	"stt", telescope stt;
	"result", telescope result
      ] )
  ));
  result

(* replace [c] with rel [k] in [tele] *)
let rec anti_subst_telescope c k tele =
  match tele with
  | [] -> []
  | (name,None,ty):: tele ->
   (name, None, Termops.replace_term c (Term.mkRel k) ty)
   :: anti_subst_telescope (Term.lift 1 c) (succ k) tele
;;

(* let anti_subst_telescope c k tele = *)
(*   let result =  anti_subst_telescope c k tele in  *)
(*   Print.( *)
(*     let doc = messages  *)
(*       [ *)
(* 	"c", constr c; *)
(* 	"k", int k; *)
(* 	"tele", telescope tele; *)
(* 	"result", telescope result *)
(*       ] in  *)
(*     let doc = prefix 2 2 (string "anti_subst") doc  in  *)
(*     eprint doc *)
(*   ); *)
(*   result *)

(* [args] is telescope of the arguments;
   [n] should be the length of the rel_context of the arguments of the inductive *)
let rec iter_tele args n tele =
  match args with
  | [] -> tele
  | t :: q ->
    let tele = anti_subst_telescope t n tele in
    iter_tele q (pred n) tele

let iter_tele args n tele =
  let result = iter_tele args n tele in
  Print.(
    let doc = messages
      [
	"args", separate_map semi constr args;
	"n", int n;
	"tele", telescope tele;
	"result", telescope result;
      ] in
    let doc = prefix 2 2 (string "iter") doc  in
    eprint doc
  );
  result

let new_sort env ind_family =
  let (_,sort_family) = Inductiveops.get_arity env ind_family in
  let sort = Termops.new_sort_in_family sort_family in
  sort


let rec diag env sigma (leaf_ids: Subst.name list)
    (split_trees: split_tree list)
    (return_type: Term.types)
    (concl: Term.constr)
    =

  (* The identifier list, the split tree list, and the typing
     telescope are all in the same order. The putative invariants of
     this code are:
  *)
    Print.(
      let doc = messages
	["stl", print_split_tree_list split_trees;
	 "return_type", constr return_type;
	 "ids", separate_map semi Subst.pp_name leaf_ids;
	 "concl", constr concl;
	]
      in
      let msg = surround 2 2 (string "begin") doc (string "end") in
      eprint msg
    );

    match split_trees with
    | [] -> (* Not dependent inductive *)
      let () = assert (CList.is_empty leaf_ids) in
      concl

    | head::ll ->
      let (name_argx,ty_argx,return_type) = Term.destProd
	  (Reductionops.whd_betaiota sigma return_type) in
      (* The first thing to do is to introduce the variable we are
	 working on and do the lift accordingly.

	 This variable has type [ty_argx] == [I pi ai].
      *)
      Term.mkLambda (name_argx,ty_argx,
	  let env = Environ.push_rel (name_argx,None,ty_argx) env in
	  let vars = List.map (Subst.lift_name 1) leaf_ids in
	  let concl = Term.lift 1 concl in

	  match head with
	  | None -> (* A variable is reached *)
	    begin match vars with
	    | [] -> Errors.anomaly (Pp.str "build: Less variable than split_tree leaves")
	    |id_h :: id_q ->
	      diag env sigma
		(List.map (fun x -> if Subst.eq_name x id_h then Subst.Rel 1 else x)
		   id_q) ll return_type
		(Subst.apply [id_h, Term.mkRel 1]  concl)
	    end
	  | Some (ind, constructor, params, split_trees) -> (* we want to refine in the [constructor] constructor case. *)
	    let ind_family = Inductiveops.make_ind_family (ind, params) in
	    let case_info = Inductiveops.make_case_info env ind Term.RegularStyle in
	    let (constructors: Inductiveops.constructor_summary array) =
	      Inductiveops.get_constructors env ind_family in
	    (* We need to build the return clause and the branches.

	       Let's take the example where we match on v: vector (S
	       n), to build the predicate P n v

	       The return clause is:
	       fun k => match k with
	       | 0 => fun v => False -> True
	       | S m => fun v => P (S m) v -> Type
	       end

	       The branches should be:
	       nil => False -> True
	       cons m x q : vector (S m) => P m (cons m x q)
	    *)

	    (* We transform the return clause in a recursive call to
	       [invert]. The thing to invert is the argment we destruct on
	       and the conclusion we want is [forall stt -> Type] *)
	    let return_clause =
	      (* In our running example, ind_args is [S @1] and ctx is
		 [vector @1; nat]. Then, we must lift the arguments by
		 one to account for the introduction of the "as" clause
		 that we represent as Rel 1. *)
	      let ind_args = snd (Term.decompose_app ty_argx) in
	      let ind_args = List.map (Term.lift 1) ind_args in
	      let split_trees,leaves =
		make_a_pattern env sigma (ind_args@[Term.mkRel 1]) in
	      let sort = new_sort env ind_family in
	      let return_clause_type =
		Inductiveops.make_arity env true ind_family sort in

	      (* morally, this is prepare_conclusion_type *)
	      let vars' = List.map (function LVar x -> Subst.Var x | LRel x -> Subst.Rel x) leaves in
	      let result = diag env sigma vars' split_trees return_clause_type return_type in
	      (* put the result in eta long form *)
	      let ctx =	Inductiveops.make_arity_signature env true ind_family in
	      let lifted_result = Term.lift (Term.rel_context_length ctx) result in
	      let result' =
		Termops.it_mkLambda_or_LetIn
		  (Reductionops.whd_beta sigma
		     (Term.mkApp (lifted_result,Termops.extended_rel_vect 0 ctx))) ctx in
	      Print.(
	      	let doc = messages
	      	  [
		    "args", separate_map semi constr ind_args;
		    "vars", separate_map semi Subst.pp_name vars';
	      	    "ctx", rel_context ctx;
	      	    "split_trees", print_split_tree_list split_trees;
	      	    "leaves", separate_map semi Subst.pp_name vars';
	      	    "concl", constr concl;
	      	    "result", constr result;
	      	    "result2", constr result';
	      	  ]
	      	in eprint (prefix 2 2 (string "return_clause") doc)
	      );
	      result' in (*we have the return clause *)

	    let branches =
	      Array.mapi
		(fun i cs ->
		  (**
		      We normalize the application of the return
		      clause to the arguments of the current branch:
		      this yields a rel_context and a term.

		     If the rel_context ends by False, it means that we can
		      instantiate this branch with False_rect.
		     Else the end of the rel_context is a correct raffinement of
		     stt that we use in reccursive call *)
		  let lifted_return =
		    Term.lift cs.Inductiveops.cs_nargs return_clause in
		  let branch_pre_ty =
		    Term.mkApp (lifted_return, cs.Inductiveops.cs_concl_realargs) in
		  let branch_ty = Term.mkApp
		    (branch_pre_ty, [|Inductiveops.build_dependent_constructor cs|]) in
		  let (specialized_ctx,expectation) =
		    Reductionops.splay_prod_assum env sigma branch_ty in

		  let real_body =
		    if i + 1 = constructor
		    then (* recursive call *)
		      diag env sigma vars (split_trees@ll)
			(Termops.it_mkProd_or_LetIn branch_ty cs.Inductiveops.cs_args)
			concl
		    else
		      (* otherwise, in the underscore case, we return
			 [False -> True] *)
		      Term.it_mkLambda_or_LetIn
			devil
			(List.append specialized_ctx cs.Inductiveops.cs_args)
 		  in
		  match specialized_ctx with
		    | (_,_,ty) :: _
			when Reductionops.is_conv env sigma ty
			  (Util.delayed_force Coqlib.build_coq_False) ->
		      Term.it_mkLambda_or_LetIn
			(Term.mkApp
			   (Lazy.force false_rect, [|expectation; Term.mkRel 1|]))
			specialized_ctx
		    | _ -> real_body
		)
		constructors
	    in
	    Term.mkCase (case_info,return_clause,Term.mkRel 1,branches)
	)

(** Debug version, that only try to construct the diag *)
let pose_diag h name gl =
  let env = Tacmach.pf_env gl in
  let sigma = Tacmach.project gl in
  let h_ty = Tacmach.pf_get_hyp_typ gl h in

  (* get the name of the inductive and the list of arguments it is applied to *)
  let (ind_family, real_args) =
    Inductiveops.dest_ind_type (Inductiveops.find_rectype env sigma h_ty) in
  let (_,sort_family) = Inductiveops.get_arity env ind_family in
  let (split_trees,leaves) = make_a_pattern env sigma (real_args @ [ Term.mkVar h]) in
  let (leaves_ids,generalized_hyps,concl) = prepare_conclusion_type gl leaves in
  let sort = Termops.new_sort_in_family sort_family in
  let return_type =(Inductiveops.make_arity env true ind_family sort) in
  let diag = diag env sigma leaves_ids split_trees return_type concl in
  Print.(eprint (stripes( string "final diag") ^/^ constr diag));
  cps_mk_letin "diag" diag (fun k -> Tacticals.tclIDTAC) gl


let invert h gl =
  let env = Tacmach.pf_env gl in
  let sigma = Tacmach.project gl in
  let h_ty = Tacmach.pf_get_hyp_typ gl h in

  (** ensures that the name x is fresh in the _first_ goal *)
  let (!!) x = Tactics.fresh_id [] ((Names.id_of_string x)) gl in
 (* get the name of the inductive and the list of arguments it is applied to *)
  let (ind_family, real_args) =
    Inductiveops.dest_ind_type (Inductiveops.find_rectype env sigma h_ty) in
  let (_,sort_family) = Inductiveops.get_arity env ind_family in
  let (split_trees,leaves) = make_a_pattern env sigma (real_args @ [Term.mkVar h]) in
  let (leaves_ids,generalized_hyps,concl) = prepare_conclusion_type gl leaves in
  let sort = Termops.new_sort_in_family sort_family in
  let return_type = Inductiveops.make_arity env true ind_family sort in
  let diag = diag env sigma leaves_ids split_trees return_type concl in
  (* Each branch is a pair: type of the subgoal, body of the branch *)
  let constructors = Inductiveops.get_constructors env ind_family in
  let branches diag =
    Array.map
      (fun cs ->
	let ctx = cs.Inductiveops.cs_args in
	(* Print.(eprint (group (string "branches/ctx" ^/^ group (rel_context ctx)))); *)
	let t = Term.mkApp (diag, cs.Inductiveops.cs_concl_realargs) in
	let t = Term.mkApp (t, [| Inductiveops.build_dependent_constructor cs |]) in
	let ty = Term.it_mkProd_or_LetIn t ctx in
	let body p = p
	in
	ty, body
      )
      constructors
  in
  Print.(eprint (stripes( string "final diag") ^/^ constr diag));
  cps_mk_letin "diag" diag
    (fun diag ->
      let branches = branches (Term.mkVar diag) in
      assert_vector
	(Array.map fst branches)
	(
	  Tacticals.tclTHENLIST
	    [Tactics.unfold_constr (Globnames.VarRef diag);
	     Tactics.clear [diag; h]
	    ])
	(fun vect gl ->
	  let env = Tacmach.pf_env gl in
	  (* extra information for the match *)
	  let ind = fst (Inductiveops.dest_ind_family  ind_family) in
	  let case_info = Inductiveops.make_case_info env ind  Term.RegularStyle in
	  let return_clause =
	    let ctx = (Inductiveops.make_arity_signature env true ind_family) in
	    Term.it_mkLambda_or_LetIn
	      (Term.mkApp (Term.mkVar diag, Termops.extended_rel_vect 0 ctx))
	      ctx
	  in
	  let term =
	    Term.mkCase
	      (case_info,
	       return_clause,
	       Term.mkVar h,
	       Array.mapi
		 (
		   fun i (_,t) ->
		     (t (Term.mkVar vect.(i)))
		 ) branches
	      )
	  in
	  Tactics.refine term gl
	)
    ) gl





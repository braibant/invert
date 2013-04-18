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

  (* let apply subst term = *)
  (*   let result = apply subst term in  *)
  (*   Print.(let doc = messages ["term", constr term; "result", constr result; "susbt", pp_t subst] in  *)
  (* 	   let doc = prefix 2 2 (string "apply") doc in  *)
  (* 	   eprint doc); *)
  (*   result *)
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


let debug (st: split_tree list) =
  let open Print in 
  let rec aux = function 
    | None -> string "#"
    | Some (ind, constructor, params, split_trees) ->
      group
	(constr (Term.mkConstruct (ind, constructor)) 
	 ^/^
	   braces (separate_map comma constr params)
	 ^/^	   
	   brackets (separate_map comma aux split_trees)
	)
  in 
  surround_separate_map 2 2
    (brackets empty) 
    lbracket
    (break 1)
    rbracket
    aux 
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

(* smart constructor *)
let mkApp term args =
  let mkApp t x =
    match Term.kind_of_term t with 
    | Term.Prod (_,_,b) -> Term.subst1 x b
    | Term.Lambda (_,_,b) -> Term.subst1 x b
    | _ -> Term.mkApp (t,[|x|])
  in   
  Array.fold_left mkApp term args



let new_sort env ind_family =   
  let (_,sort_family) = Inductiveops.get_arity env ind_family in
  let sort = Termops.new_sort_in_family sort_family in 
  sort

let diag env sigma (leaf_ids: Subst.name list)
    (split_trees: split_tree list) 
    (split_tree_types: Telescope.t)
    (concl: Term.constr) sort
    =

  (* The identifier list, the split tree list, and the typing telescope are all in the same order *)
  let rec build env 
      concl
      sort
      (identifier_list: Subst.name list)
      (stl : split_tree list)
      (stt: Telescope.t)
      =
    Print.(
      let doc = messages 
	["stl", debug stl;
	 "stt", telescope stt;
	 "ids", separate_map semi Subst.pp_name identifier_list;
	 "concl", constr concl
	]
      in      
      let msg = surround 2 2 (string "begin") doc (string "end") in
      eprint msg
    );    
    match stl, stt with
    | [], [] -> (* Not dependent inductive *)
      let () = assert (CList.is_empty identifier_list) in
      concl
    | ll, ((_,Some _,_) as decl)::stt ->      
      Printf.eprintf "Warning: constructor with let_ins in inversion/build.\n";
      let term = build env concl sort identifier_list stl stt in 
      Term.mkLambda_or_LetIn decl (Term.lift 1 term) 
    | head::ll, ((name_argx,None,ty_argx) as decl) ::stt ->
      (* let subst = lift_subst 1 subst in *)
      (* The first thing to do is to introduce the variable we are
	 working on.  
	 
	 This variable as type [ty_argx] == [I pi ai]. 
      *)
      Term.mkLambda_or_LetIn decl 
	(
	  match head with 	       
	  | None ->
	    begin match identifier_list with
	    | [] -> Errors.anomaly (Pp.str "build: Less variable than split_tree leaves")
	    |id_h :: id_q ->
	      build env 
		(Subst.apply [id_h, Term.mkRel (List.length stt + 1)]  (concl))
		sort
		(List.map (fun x ->
		  if Subst.eq_name x id_h 
		  then Subst.Rel 1 
		  else (* match x with Subst.Rel 1 -> x | _ -> *) Subst.lift_name 1 x) id_q) ll stt
	    end
	  | Some (ind, constructor, params, split_trees) ->
	    let ind_family = Inductiveops.make_ind_family (ind, params) in
	    let case_info = Inductiveops.make_case_info env ind Term.RegularStyle in
	    let (constructors: Inductiveops.constructor_summary array) =
	      Inductiveops.get_constructors env ind_family in
	    
	    (* We need to build the return clause and the branches.
	       
	       Let's take the example where we match on v: vector (S
	       n), to build the predicate P (S n) v
	       
	       There are two possibilities for  the return clause.	      

	       First, consider: fun m => fun (v: vector m) => P m v -> Type
	       
	       In that case, the branches should be :
	       nil => fun _ : P 0 nil => ...
	       cons m x q =>  fun _ : P (S m) (cons m x q) => ...
	       
	       Another possibility for the return clause is:
	       fun m => fun v => match m with 0 => False -> True | S m => P (S m) v -> Type end

	       In that case the branches should be:
	       nil => False -> True
	       cons m x q : vector (S m) => P (S m) (cons m x q)  
	       
	       Let's implement the first strategy: we have to replace
	       the occurences of the arguments of the inductive in the
	       telescope by the "correct" de Bruijn variables. For
	       instance, we have to replace (S n) by m. *)
	    
	    (* In our running example, ind_args is [S @1] and ctx is [vector @1; nat]*)
	    let ind_args = try  Array.to_list (snd (Term.destApp ty_argx)) with _ -> [] in 
	    
	    (* [ctx] is the (dependent) arity of the inductive we
	       destruct on. *)
	    let ctx = Inductiveops.make_arity_signature env true ind_family in
	    
	    let _ = 
	      Print.(
		let doc = messages 
		  [
		    "ind_args", separate_map semi constr ind_args;
		    "ctx", rel_context ctx
		  ]
		in eprint doc
	      )
	    in 
	    (* Then, we refine the [stt] to take into account the
	       generalization of the [match ... as ... in ...]. First,
	       we must lift the arguments of the inductive by 1 to
	       account for the [fun decl] that we introduced above. *)
	    let stt =
	      let ind_args = List.map (Term.lift 1) ind_args in 	    
	      let n = (Term.rel_context_nhyps ctx) in 
	      iter_tele (List.map (Term.lift n) ind_args) n (Telescope.lift_above 2 n stt)
	    in 	
	    
	    (* At this point, we wonder what is the equivalent of the
	       above transformation on the conclusion. *)
	    
	    
	    (* We transform the return clause in a recursive call to
	       [build]: we start by making a call to make_a_pattern
	       with the arguments of the type of [decl] and the
	       conclusion being the [stt]. First, we must substitute
	       fresh variables for each de Bruijn indices. *)

	    let return_clause = 
	      let ctx' = Inductiveops.make_arity_signature env true ind_family in 
	      let env = Environ.push_rel_context ctx' env in
	      let split_trees,leaves = 
		(* let n = Term.rel_context_nhyps ctx' in  *)
		let n = 1 in 
		make_a_pattern env sigma ((List.map (Term.lift n) ind_args)@[Term.mkRel 1]) in
	      (* let split_trees,leaves = make_a_pattern env sigma ind_args in *)
	      (* morally, this is prepare_conclusion_type *)
	      let vars' = List.map (function LVar x -> Subst.Var x | LRel x -> Subst.Rel x) leaves in
	      let concl =  Term.mkArity (List.rev stt,sort)  in 
	      let sort = new_sort env ind_family in 
	      let result = build env concl sort vars' split_trees (List.rev ctx') in
	      (* let result = Termops.it_mkLambda_or_LetIn result ctx in *)
	      let result' = 
		Termops.it_mkLambda_or_LetIn (mkApp result  (Termops.extended_rel_vect 0 ctx)) ctx in 
	      Print.(
	      	let doc = messages
	      	  [
	      	    "stt", telescope stt;
		    "args", separate_map semi constr ind_args;
	      	    "vars", separate_map semi Subst.pp_name identifier_list;
	      	    "ctx", rel_context ctx;
	      	    "ctx'", rel_context ctx';
	      	    "split_trees", debug split_trees;
	      	    "leaves", separate_map semi Subst.pp_name vars';
	      	    "concl", constr concl;
	      	    "result", constr result;
	      	    "result2", constr result';
	      	  ]
	      	in eprint (prefix 2 2 (string "return_clause") doc)
	      );
	      result'
	      
	    in 
	    let branches =
	      Array.mapi
		(fun i cs ->
		  (* substitude the matched term (Rel 1) by the constructor in the branch we are *)
		  let args = Inductiveops.build_dependent_constructor cs
		    :: Array.to_list cs.Inductiveops.cs_concl_realargs in 
		  let concl = Term.lift (Array.length cs.Inductiveops.cs_concl_realargs) concl in
		  let stt,concl = 
		    (* let before = Print.(messages ["stt", telescope stt; "concl", constr concl]) in  *)
		    let ctx = List.rev stt in 
		    let ctx = Term.add_rel_decl (Names.Anonymous, None, concl) ctx in
		    let (_,_,concl)::ctx = Termops.substl_rel_context args  ctx in 
		   (*  Print.( *)
		   (*    let after = messages  *)
		   (*     [ *)
		   (* 	 "stt'", telescope (List.rev ctx); *)
		   (* 	 "concl", constr concl;			  *)
		   (*     ] *)
		   (*   in  *)
		   (*   let doc = prefix 2 2 (string "before") before ^^ hardline ^^ *)
		   (*     prefix 2 2 (string "after") after ^^ hardline in  *)
		   (*   eprint doc *)
		   (* ); *)
		    (* let ctx = Termops.lift_rel_context (-1) ctx in  *)
		    List.rev ctx, concl
		  (* List.rev (Termops.substl_rel_context args (List.rev stt)) *)
		  in


		  (** We may instantiate the body of the branch by the
		      daemon, based on the following idea.

		      We normalize the application of the return
		      clause to the arguments of the current branch:
		      this yields a rel_context and a term. If the
		      rel_context contains False, it means that we can
		      instantiate this branch with False_rect.		      
		  *)
		  
		  let elim_body = 
		    let app = Term.mkApp (return_clause, Array.of_list (List.rev args)) in   
		    let (ctx,concl) = Reductionops.splay_prod_assum env sigma app in
		    match ctx with 
		    | [] -> None
		    | (_,_,ty) :: q  when Reductionops.is_conv env sigma ty (Util.delayed_force Coqlib.build_coq_False)   -> Some (ctx,concl)
		    | _ -> None
		      
		  in 
		  
		  let real_body =
		    if i + 1 = constructor
		    then
		      begin
			let env' = Environ.push_rel_context cs.Inductiveops.cs_args env in
			let term =
			  build env' 
			    (concl)
			    sort
			    (List.map (Subst.lift_name 1) identifier_list)
			    (split_trees@ll)
			    (List.rev_append cs.Inductiveops.cs_args stt)
			in
			term
		      end
		    else
		      (* otherwise, in the underscore case, we return
			 [False -> True] *)
		      Term.it_mkLambda_or_LetIn
			devil
			(List.rev_append stt cs.Inductiveops.cs_args)
 		  in	      
		  match elim_body with 
		  | None -> real_body
		  | Some (ctx,q) -> 
		    Term.it_mkLambda_or_LetIn  (Term.mkApp (Lazy.force false_rect, [|q; Term.mkRel 1|])) ctx
		)
		constructors
	    in 	    
	    Term.mkCase (case_info,return_clause,Term.mkRel 1,branches)
	)
  in
  build env  concl sort leaf_ids split_trees split_tree_types 

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
  let ctx =(Inductiveops.make_arity_signature env true ind_family) in
  let diag = diag env sigma leaves_ids split_trees (List.rev ctx)  concl sort in
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
  let ctx = Inductiveops.make_arity_signature env true ind_family  in
  let sort = Termops.new_sort_in_family sort_family in
  let diag = diag env sigma leaves_ids split_trees (List.rev ctx)  concl sort in
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





open Invertlib


(* Given an term [term] in type [I params {args}], build a case of return clause
   [return_clause] feeding the impossible branch with a correct term and calling
   [kf] constructor_number constructor_spec expected_type extracted_rel_context
   for others. *)
let mk_casei env sigma ind params term return_clause kf =
  let ind_family = Inductiveops.make_ind_family (ind, params) in
  let case_info = Inductiveops.make_case_info env ind Constr.RegularStyle in
  let (constructors: Inductiveops.constructor_summary array) =
    Inductiveops.get_constructors env ind_family in
  let branches =
    Array.mapi (fun i cs ->
      (**
	 We normalize the application of the return
	 clause to the arguments of the current branch:
	 this yields a rel_context and a term.

	 If the rel_context ends by False, it means that we can
	 instantiate this branch with False_rect.
	 Else the continuation function is called. *)
      let lifted_return =
	Vars.lift cs.Inductiveops.cs_nargs return_clause in
      let branch_pre_ty =
	Constr.mkApp (lifted_return, cs.Inductiveops.cs_concl_realargs) in
      let branch_ty = Constr.mkApp
	(branch_pre_ty, [|Inductiveops.build_dependent_constructor cs|]) in
      let (specialized_ctx,expectation) =
	Reductionops.splay_prod_assum env sigma branch_ty in
      match specialized_ctx with
      | (_,_,ty) :: _
	  when Reductionops.is_conv env sigma ty
	    (Util.delayed_force Coqlib.build_coq_False) ->
	Term.it_mkLambda_or_LetIn
	  (Constr.mkApp
	     (Lazy.force false_rect, [|expectation; Constr.mkRel 1|]))
	  specialized_ctx
      | _ -> kf i cs branch_ty specialized_ctx
    )
      constructors
  in
  Constr.mkCase (case_info,return_clause,term,branches)

let mk_case_tac ind_family term return_clause subtac k = fun gl ->
  let ind = fst (Inductiveops.dest_ind_family ind_family) in
  let env = Tacmach.pf_env gl in
  let sigma = Tacmach.project gl in
  let case_info = Inductiveops.make_case_info env ind Constr.RegularStyle in
  let (constructors: Inductiveops.constructor_summary array) =
    Inductiveops.get_constructors env ind_family in
  let rec build i l acc : Proof_type.tactic = fun gl ->
   if i < Array.length constructors
    then
      begin
	let cs = constructors.(i) in
	let ctx = cs.Inductiveops.cs_args in
	let env' = Environ.push_rel_context ctx env in
	let lifted_return =
	  Vars.lift cs.Inductiveops.cs_nargs return_clause in
	let branch_pre_ty =
	  Constr.mkApp (lifted_return, cs.Inductiveops.cs_concl_realargs) in
	let branch_ty = Constr.mkApp
	  (branch_pre_ty, [|Inductiveops.build_dependent_constructor cs|]) in
	let (specialized_ctx,expectation) =
	  Reductionops.splay_prod_assum env' sigma branch_ty in
	let branch_ty = Term.it_mkProd_or_LetIn branch_ty ctx in
	match specialized_ctx with
	| (_,_,ty) :: _
	    when Reductionops.is_conv env sigma ty
	      (Util.delayed_force Coqlib.build_coq_False) ->
	  let body =
	    Term.it_mkLambda_or_LetIn
	      (Constr.mkApp
		 (Lazy.force false_rect, [|expectation; Constr.mkRel 1|]))
	      specialized_ctx
	  in
	  let body = Term.it_mkLambda_or_LetIn body ctx in
	  build (succ i) l (body::acc ) gl
	| _ ->
	  let name = (Names.id_of_string "invert_subgoal") in
	  let name =  Tactics.fresh_id [] name gl in
	  let t = Tactics.assert_tac  (Names.Name name) branch_ty in
	  Tacticals.tclTHENS t
	    [   Tacticals.tclTHEN (Tactics.clear l) subtac;
		  (* Tacticals.tclIDTAC; *)
		build (succ i) (name :: l) ((Constr.mkVar name) :: acc)
	    ] gl
      end
    else
      let term = Constr.mkCase (case_info, return_clause, term, (Array.of_list (List.rev acc))) in
      k term gl
  in
  build 0 [] [] gl


module ST = struct
  type name =
  | Var of Names.Id.t
  | Rel of int

  let name_to_constr = function
    | Var v -> Constr.mkVar v
    | Rel i -> Constr.mkRel i

  let lift_name n = function
    | Var name -> Var name
    | Rel i -> Rel (i + n)

  let eq_name = (=)

  type t =
  | Constructor of
      (Names.inductive * int (* constructor number *) *
	 Constr.t list (* params *) * t list)
  | Leaf of name

  let var v = Leaf (Var v)
  let rel i = Leaf (Rel i)

  let make env sigma (args: Constr.t list) : t list =
    (* Print.(eprint  *)
    (* 	     (prefix 2 2 (string "args") *)
    (* 	     (separate_map semi constr args))); *)
    let rec aux arg : t  =
      let (hd,tl) = Reductionops.whd_betadeltaiota_stack env sigma arg in
      match Constr.kind hd with
      | Constr.Var v when CList.is_empty tl -> var v
      | Constr.Rel i when CList.is_empty tl -> rel i
      | Constr.Construct (ind, i) ->
	let params,real_args = CList.chop (Inductiveops.inductive_nparams ind) tl in
	let constrs = List.map aux real_args in
	Constructor (ind, i, params, constrs)
      | _ ->
	Print.(eprint (constr hd));
	invalid_arg "todo"
    in
    List.map aux args

  let rec lift i = function
    | Leaf v -> Leaf (lift_name i v)
    | Constructor (ind, constructor, params,stl) ->
      Constructor (ind, constructor, params, List.map (lift i) stl)

  let liftl i l = List.map (lift i) l

  let rec vars = function
    | Leaf v -> [v]
    | Constructor (ind, constructor, params, stl) -> varsl stl
  and varsl stl = List.flatten (List.map vars stl)

  (* decrement all rel variables by one *)
  let rec pop_vars = function
    | [] -> []
    | Var name::q -> Var name :: pop_vars q
    | Rel i :: q -> if i > 1 then Rel (i - 1) :: pop_vars q else  pop_vars q

  let pp_name = let open Print in
		function
		| Rel i -> string "@" ^^ int i
		| Var v -> id v

  let pp_t t =
  let open Print in
  let rec aux t =
    match t with
    | Leaf n -> pp_name n
    | Constructor (ind, constructor, params, split_trees) ->
      group
	(constr (Constr.mkConstruct (ind, constructor))
	 ^^
	   (surround_separate_map 2 1 (break 1) (break 1 ^^ lbrace) comma (rbrace ^^ break 1) constr params)
	 ^^
	   brackets (separate_map comma aux split_trees)
	)
  in aux t

  let pp_tl (st: t list) =
    let open Print in
    surround_separate_map 2 1
      (brackets empty)
      lbracket
      (semi ^^ break 1)
      rbracket
      pp_t
      st

end

module Subst = struct
  type t = Names.Id.t list * int list * Context.rel_context
(** var to abstract * rels to substitute the var with * rel_context of the var list

The 3 list have the same length ... *)

  let empty = ([],[],[])

  let pp (vars,rels,ctx) =
  Print.(
    let doc = messages
      [
       "ctx", (rel_context ctx);
       "vars", (surround_separate_map 2 1 (break 0) (lbrace) comma (rbrace) constr vars);
       "rels", (surround_separate_map 2 1 (break 0) (lbrace) comma (rbrace) int rels);
      ]
    in
    surround 2 2 (string "begin subst") doc (string "end")
  )

  (** [subst_in_type_when_possible env sigma ctx vars args t] substitutes
      [vars] by [args] in [t]. Rel context created by the [vars] is [ctx].
  *)
  let subst_in_type_when_possible env sigma ctx vars args t =
  Print.(
    let doc = messages
      ["t", constr t;
       "ctx", (rel_context ctx);
       "vars", (surround_separate_map 2 1 (break 0) (lbrace) comma (rbrace) constr vars);
       "args", (surround_separate_map 2 1 (break 0) (lbrace) comma (rbrace) constr (Array.to_list args));
      ]
    in
    let msg = surround 2 2 (string "begin") doc (string "end") in
    eprint msg
  );

    if CList.is_empty vars then t else
    let abstracted_ty = Term.mkArity (ctx,Termops.new_Type_sort ()) in
    let abstracted =
      Unification.abstract_list_all_with_dependencies
	env sigma abstracted_ty t vars in
    Reductionops.whd_beta sigma (Constr.mkApp (abstracted,args))

  let traverse_to_add env sigma term lazy_decl to_translate (vars,rels,ctx) =
      let rec aux a b = match a, b with
	| hv :: tv, _ :: tr when Constr.equal term hv -> a, 1 :: tr, ctx
	| hv :: tv, hr :: tr ->
	  let tv',tr',ctx' = aux tv tr in
	  (hv::tv',(to_translate hr)::tr',ctx')
	| [], [] ->
	  let (name,_,ty) = lazy_decl () in
	  let new_ty =
	    subst_in_type_when_possible env sigma ctx vars
	      (Termops.extended_rel_vect 0 ctx) ty in
	  ([term], [1], Context.add_rel_decl (name, None, new_ty) ctx)
	| _, _ ->
	  Errors.anomaly ~label:"Invert_tactic.Subst.traverse_to_add"
	    (Pp.str "Broken substitution")
      in aux vars rels

  let add env sigma subst = function
    | ST.Rel i ->
      let i_t = Constr.mkRel i in
      let lazy_decl () =
	let x, y, z = Environ.lookup_rel i env in x, y, Vars.lift i z in
      traverse_to_add env sigma i_t lazy_decl
	(fun x -> if Int.equal x i then 1 else x) subst
    | ST.Var v ->
      let v_t = Constr.mkVar v in
      let lazy_decl () = (Names.Name v, None, Environ.named_type v env) in
      traverse_to_add env sigma v_t lazy_decl (fun x -> x) subst

  let lift k (vars,rels,ctx) =
    (CList.map (Vars.lift k) vars,CList.map ((+) k) rels,ctx)

  let subst_in_type env sigma (vars,rels,ctx) t =
    subst_in_type_when_possible env sigma ctx vars
      (CArray.map Constr.mkRel (CArray.of_list rels)) t

end

let rec split_tree2diag
    env sigma subst
    (split_trees: ST.t list)
    (return_type: Constr.types)
    (concl: Constr.t)
    =
  Print.(
    let doc = messages
      ["subst", Subst.pp subst;
	"stl", ST.pp_tl split_trees;
       "return_type", constr return_type;
       "concl", constr concl;
      ]
    in
    let msg = surround 2 2 (string "begin") doc (string "end") in
    eprint msg
  );

  let split_trees = ST.liftl 1 split_trees in
  match split_trees with
  | [] -> Subst.subst_in_type env sigma subst concl
  | head::ll ->
    let (name_argx,ty_argx,return_type) =
	Term.destProd
	  (Reductionops.whd_betaiotazeta sigma return_type)
    in

    (* The first thing to do is to introduce the variable we are
       working on and do the lift accordingly.

       This variable has type [ty_argx] == [I pi ai].  *)
    Constr.mkLambda
      (name_argx,ty_argx,
       let lifted_env = Environ.push_rel (name_argx,None,ty_argx) env in
       let concl = Vars.lift 1 concl in
       let lifted_subst = Subst.lift 1 subst in

       match head with
       | ST.Leaf v ->
	 split_tree2diag lifted_env sigma (Subst.add lifted_env sigma lifted_subst v)
	   ll return_type concl
       | ST.Constructor (ind, constructor, params, split_trees) ->
	 (* we want to refine in the [constructor] constructor case. *)
	 (* We need to build the return clause and the branches.

	    Let's take the example where we match on v: vector (S n),
	    to build the predicate P n v

	    The return clause is: fun k => match k with | 0 => fun v
	    => False -> True | S m => fun v => P (S m) v -> Type end

	    The branches should be: nil => False -> True cons m x q :
	    vector (S m) => P m (cons m x q) *)

	 (* We transform the return clause in a recursive call to
	    [invert]. The thing to invert is the argment we destruct
	    on and the conclusion we want is [forall stt -> Type] *)

	 let return_clause,args =
	   matched_type2diag lifted_env sigma (Constr.mkRel 1)
	     (Vars.lift 1 ty_argx) return_type in (*we have the return clause *)
	 let real_body i cs branch_ty specialized_ctx =
	   if i + 1 = constructor
	   then (* recursive call *)
	     split_tree2diag lifted_env sigma lifted_subst
	       (split_trees@List.map (fun x -> ST.Leaf x) args@ll)
	       (Termops.it_mkProd_or_LetIn branch_ty cs.Inductiveops.cs_args)
	       concl
	   else
	     (* otherwise, in the underscore case, we return
		[False -> True] *)
	     Term.it_mkLambda_or_LetIn
	       devil
	       (List.append specialized_ctx cs.Inductiveops.cs_args)
 	 in
	 Term.applistc
	   (mk_casei lifted_env sigma ind params (Constr.mkRel 1) return_clause real_body)
	   (List.map ST.name_to_constr args)
      )
and matched_type2diag env sigma (tm: Constr.t) ty pre_concl =
  let (ind_family, real_args) =
    Inductiveops.dest_ind_type (Inductiveops.find_rectype env sigma ty) in
  let (_,sort_family) = Inductiveops.get_arity env ind_family in
  let split_trees = ST.make env sigma (real_args @ [ tm ]) in
  let generalized_hyps,concl = prepare_conclusion env pre_concl split_trees  in
  let sort = Termops.new_sort_in_family sort_family in
  let return_type = Inductiveops.make_arity env true ind_family sort in
  let result = split_tree2diag env sigma Subst.empty split_trees return_type concl in
  (* put the result in eta long form *)
  let ctx = Inductiveops.make_arity_signature env true ind_family in
  let lifted_result = Vars.lift (Context.rel_context_length ctx) result in
  let result' =
    Termops.it_mkLambda_or_LetIn
      (Reductionops.whd_beta sigma
	 (Constr.mkApp (lifted_result,Termops.extended_rel_vect 0 ctx))) ctx in
  result', generalized_hyps
and prepare_conclusion env concl stl : ST.name list * Constr.t =
  let ctx0 = Environ.rel_context env in
  let ctx1 = Environ.named_context env in

  let rec occurs_check ty vars  =
    match vars  with
    | [] -> false
    | ST.Rel i :: vars ->  Termops.dependent (Constr.mkRel i) ty || occurs_check ty vars
    | ST.Var v :: vars ->  Termops.dependent (Constr.mkVar v) ty || occurs_check ty vars
  in
  (* Fold on a rel-context *)
  let rec fold_ctx ctx vars args term pos add =
    match ctx with
    | [] -> args, term
    | ((name, None, ty) as decl)::q ->
      let vars' = ST.pop_vars vars in
      if occurs_check ty vars'
      then
  	let args' = ST.Rel pos :: args in
	let term' = Vars.lift 1 term in
	let term'' = Termops.replace_term (Constr.mkRel (add + 1)) (Constr.mkRel 1) term' in
	fold_ctx q vars' args' (Constr.mkProd (name, Vars.lift pos ty, term'')) (succ pos) (succ add)
      else
  	fold_ctx q vars' args term (succ pos) add
    | _ -> assert false
  in
  (* fold on named-context *)
  let rec fold_names ctx vars args term =
    match ctx with
    | [] -> args, term
    | ((id, None, ty) as decl)::q ->
      if occurs_check ty vars && not (List.mem (ST.Var id) vars)
      then
  	let args' = ST.Var id :: args in
  	let term' = Vars.lift 1 term in
  	let term'' = Termops.replace_term (Constr.mkVar id) (Constr.mkRel 1) term' in
  	fold_names q vars args' (Constr.mkProd (Names.Name id, ty, term''))
      else
  	fold_names q vars args term
    | ((id, Some body, ty) as decl)::q ->
      if occurs_check ty vars && not (List.mem (ST.Var id) vars)
      then
  	let term' = Vars.lift 1 term in
  	let term'' = Termops.replace_term (Constr.mkVar id) (Constr.mkRel 1) term' in
  	fold_names q vars args (Constr.mkLetIn (Names.Name id, ty, body, term''))
      else
  	fold_names q vars args term
    | _ -> assert false
  in
  let vars = ST.varsl stl in
  match ctx0 with
  | [] -> fold_names ctx1 vars [] concl
  | _::ctx -> fold_ctx ctx (ST.pop_vars vars) [] concl 2 2

(** Debug version, that only try to construct the diag *)
let pose_diag h name gl =
  let env = Tacmach.pf_env gl in
  let sigma = Tacmach.project gl in
  let h_ty = Tacmach.pf_get_hyp_typ gl h in
  let pre_concl = Tacmach.pf_concl gl in
  (* get the name of the inductive and the list of arguments it is applied to *)
  let diag,_ = matched_type2diag env sigma (Constr.mkVar h)
    h_ty pre_concl in
  Print.(eprint (stripes( string "final diag") ^/^ constr diag));
  cps_mk_letin "diag" diag (fun k -> Tacticals.tclIDTAC) gl

let invert h gl =
  let env = Tacmach.pf_env gl in
  let sigma = Tacmach.project gl in
  let h_ty = Tacmach.pf_get_hyp_typ gl h in
  let pre_concl = Tacmach.pf_concl gl in
  (** ensures that the name x is fresh in the _first_ goal *)
  let (!!) x = Tactics.fresh_id [] ((Names.id_of_string x)) gl in
  (* get the name of the inductive and the list of arguments it is applied to *)
  let diag,l = matched_type2diag env sigma (Constr.mkVar h) h_ty
    pre_concl in
  (* Each branch is a pair: type of the subgoal, body of the branch *)
  let (ind_family, _) = Inductiveops.dest_ind_type
    (Inductiveops.find_rectype env sigma h_ty) in

      let subtac =
	   Tactics.clear (h :: (List.fold_left (fun acc x ->
	       match x with
	       | ST.Var n -> n::acc
	       | _ -> acc
	     ) [] l))
      in
      mk_case_tac ind_family (Constr.mkVar h) diag subtac
	(
	  fun term ->
	    let term = Term.applistc term (List.map ST.name_to_constr l) in
	    Tactics.refine term
	) gl

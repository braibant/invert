open Invertlib

type split_tree =
  ((Names.inductive * int (* constructor number *) *
      Term.constr list (* params *) * 'a list) option as 'a)
      
  
type split_tree_leaf =
  | LVar of Names.identifier
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
let make_a_pattern env sigma args : split_tree list * split_tree_leaf list =
  let rec aux t vars =
    let (hd,tl) = Reductionops.whd_betadeltaiota_stack env sigma t in
    match Term.kind_of_term hd with
    | Term.Var v when CList.is_empty tl -> (None, (LVar v) :: vars)
    | Term.Construct (ind, i) ->
      let params,real_args = CList.chop (Inductiveops.inductive_nparams ind) tl in
      let (constrs,leafs) =
	CList.fold_map' aux real_args vars in
      (Some (ind, i, params, constrs), leafs)
    | _ -> (None, (LTerm t) :: vars)
  in
  let (a, b) = CList.fold_map' aux args [] in
  (a, b)

(** From the split_tree_leave list, we build an identifier list by generating
    variables y_s for the LTerm t_s.

    We must be able to substitute the t_s in the goal by the y_s: concl' =
    goal[y_s/t_s] must be typable.

    We must also generalize hypotheses not present in split_tree_leave that depends
    on an element of split_tree_leave to get the real conclusion
*)
let prepare_conclusion_type gl leaves =
  let vars = List.map (function LVar x -> x) leaves in 
  let concl = Tacmach.pf_concl gl in
  (vars,
   [||],
   concl)


let devil =
  Term.mkProd
    (Names.Anonymous,
     Util.delayed_force Coqlib.build_coq_False,
     Util.delayed_force Coqlib.build_coq_True)


(* Given an inductive I, and a constructor C, build the match that
   filters the constructor C, and calls the [kt] function to build a
   term; otherwise, calls the [kf] function. *)
let mk_match env sigma ind constructor params term return_clause kt kf = 
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
	    kt  args_ty 
	  else
	    kf  args_ty 
 	in
	branch_body
      )
      branches_type
  in
  let t = Term.mkCase (case_info,return_clause,term,branches) in 
  t


    

let pp_constr fmt x = Pp.pp_with fmt (Printer.pr_constr x)
let pp_id fmt x = Pp.pp_with fmt (Names.Id.print x)
let pp_gl fmt x = Pp.pp_with fmt (Printer.pr_goal x)


let diag env sigma (leaf_ids: Names.Id.t list)
    (split_trees: split_tree list)
    (split_tree_types: Term.rel_context)
    (concl: Term.constr)  concl_sort  =
  (** build the return predicate

      input :
      - leaf return clause
      - identifier list
      internally in recursive calls
      - a list of (int (* = to_lift *) * split_tree list)
      - a association list identifier -> deBruijn indice
  *)
  let rec build_diag env substitution identifier_list
      (shift: int)
      (stl : split_tree list)
      (stt: Term.rel_context) =

    match stl, stt with
    (* BUGS:
     * deal with letins in constructor args telescope
     * deal with type dependency between split trees
     * one day, do not do useless destruct: for I : forall n, Fin.t n ->
     * foo, it is useless to destruct (S m) if we have I (S m) (Fin.F1)
     *)
    | [], [] -> (* Not dependent inductive *)
      let () = assert (CList.is_empty identifier_list) in
      let _ = List.iter (fun (id,t) -> Format.eprintf "%a => %a" pp_id id pp_constr t) substitution in
      Term.replace_vars substitution (Term.lift shift concl)
    | [], _ :: _ | _ :: _, [] -> assert false
    | ll, (_,Some _,_)::stt ->
      Format.eprintf "Warning: constructor with let_ins in inversion/build_diag.\n";
      build_diag env substitution identifier_list shift stl stt
    | head::ll, (name_argx,None,ty_argx)::stt ->
      let lift_subst = List.map (fun (id, tm) -> (id, Term.lift 1 tm)) substitution in
      begin match head with
      | Some (ind, constructor, params, split_trees) ->
	let _ = Format.eprintf "C = %a, " pp_constr (Term.mkConstruct (ind,constructor)) in
	let case_info = Inductiveops.make_case_info env ind Term.RegularStyle in
	(* the type of each constructor *)
	let ind_family = Inductiveops.make_ind_family (ind, params) in
	let (constructors: Inductiveops.constructor_summary array) =
	  Inductiveops.get_constructors env ind_family in
	let branches =
	  Array.mapi
	    (fun i cs ->
	      (* substitude the matched term (Rel 1) by the constructor in the branch we are *)
	      let stt = List.rev (Termops.substl_rel_context
				    (Inductiveops.build_dependent_constructor cs
				     :: Array.to_list cs.Inductiveops.cs_concl_realargs) (List.rev stt)) in
	      let branch_body =
		if i + 1 = constructor
		then
		  begin
		    let env' = Environ.push_rel_context cs.Inductiveops.cs_args env in
		    let term =
		      build_diag env' lift_subst identifier_list
			(succ shift)
			(split_trees@ll)
			(List.rev cs.Inductiveops.cs_args@stt)
		    in
 		    (* Term.mkLambda (Names.Anonymous, ty_argx,term) *)
		    (Term.it_mkLambda_or_LetIn
		       (Term.mkApp (term, Termops.extended_rel_vect 0 cs.Inductiveops.cs_args))
		       cs.Inductiveops.cs_args)
		  end
		else
		  (* otherwise, in the underscore case,
		     we return [False -> True] *)
		  Term.it_mkLambda_or_LetIn
		    devil
		    (List.rev_append stt cs.Inductiveops.cs_args)
 	      in
	      branch_body
	    )
	    constructors
	in
	let return_clause =
	  let ctx_ind = Inductiveops.make_arity_signature env true ind_family in
	  let stt = (*Termops.lift_rel_context (Term.rel_context_nhyps ctx_ind)*) (List.rev stt) in
	  Term.it_mkLambda_or_LetIn
	    (Term.mkArity (stt, concl_sort))
	    ctx_ind
	in
	Term.mkLambda (name_argx, ty_argx,
		       Term.mkCase (case_info,return_clause,Term.mkRel 1,branches))
      | None ->
	match identifier_list with
	| [] ->
	  Errors.anomaly (Pp.str "build_diag: Less variable than split_tree leaf")
	|id_h :: id_q ->
	  Term.mkLambda (name_argx, ty_argx,
			 build_diag env ((id_h, Term.mkRel 1):: lift_subst) id_q (succ shift) ll stt
	  )
      end
  in
  build_diag env [] leaf_ids 0  split_trees split_tree_types

let diag2 env sigma (leaves_ids,generalized_hyps,concl) split_trees ind_family sort_family =
  let args_ty =
    (Inductiveops.make_arity_signature env true ind_family) in
  let return_pred =
    let ctx = List.rev args_ty in
    diag env sigma leaves_ids split_trees ctx concl (Termops.new_sort_in_family sort_family) in
  (Term.it_mkLambda_or_LetIn
     (Term.mkApp ((Term.mkApp (return_pred, generalized_hyps)),
		  Termops.extended_rel_vect 0 args_ty))
     args_ty)

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
  let constructors = Inductiveops.get_constructors env ind_family in

  let (split_trees,leaves) =
    make_a_pattern env sigma (real_args @ [Term.mkVar h]) in
  List.iter (function
  | LVar v -> Format.eprintf "variable %a, " pp_constr (Term.mkVar v)
  | LTerm t -> Format.eprintf "term %a, " pp_constr t) leaves;
  let () = Format.eprintf "\n%!" in
  let (leaves_ids,generalized_hyps,concl) =
    prepare_conclusion_type gl leaves in
  let return_pred =
    let ctx = List.rev (Inductiveops.make_arity_signature env true ind_family) in
    diag env sigma leaves_ids split_trees ctx concl (Termops.new_sort_in_family sort_family) in
  let return_clause =
    let args_ty =
      (Inductiveops.make_arity_signature env true ind_family) 
    in
    (Term.it_mkLambda_or_LetIn
       (Term.mkApp ((Term.mkApp (return_pred, generalized_hyps)),
		    Termops.extended_rel_vect 0 args_ty))
       args_ty)
  in
  let _ = Format.eprintf "diag: %a\n" pp_constr return_clause in

  (* cqssons un etage de constructeur de l'inductif *)
  let branches diag =
    Array.map
      (fun c ->
 	let ctx =  c.Inductiveops.cs_args  in
	let concl_ty = Termops.it_mkProd_or_LetIn
	    (
	      let t = Term.mkApp (diag, c.Inductiveops.cs_concl_realargs) in
	      let t = Term.mkApp (t, [| Inductiveops.build_dependent_constructor c |]) in
	      t
	    )
	    ctx
	in
	Format.eprintf "concl: %a\n" pp_constr concl_ty;

	  (* let _ = Format.printf "concl-ty: %a\n" pp_constr concl_ty in  *)
	let body subgoal =
	  let x =
	    Namegen.it_mkLambda_or_LetIn_name env
	      (Term.mkApp (subgoal, Termops.extended_rel_vect 0 ctx))
	      ctx
	  in
	  Format.eprintf "subgoal: %a\n" pp_constr x;
	  x
	  (* Termops.it_mkLambda_or_LetIn  *)
	  (* (Term.mkCast (subgoal, Term.DEFAULTcast, concl_ty)) *)
	  (*   (Term.mkCast (subgoal, Term.DEFAULTcast,concl_ty)) c.Inductiveops.cs_args *)
	in
	(concl_ty, body)
      )
      constructors
  in
  cps_mk_letin "diag" return_clause
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


  
let debug = true

let sanity env sigma t = 
  if debug 
  then 
    begin 
      Print.(eprint (string "Typing:" ^/^ Print.constr t));
      try 
	let ty = Typing.type_of env sigma t in 
	Print.(eprint (string "Type:" ^/^ Print.constr ty));
      with e -> 
	Print.(eprint (string "Unable to type the term"))
    end

let mk_fun
    (name:Names.identifier)
    (t: Term.constr)
    (k : Names.identifier -> Term.constr) =
  Term.mkNamedLambda name t (Term.subst_vars [name] (k name))

let mk_let
    (name:Names.identifier)
    (c: Term.constr)
    (t: Term.constr)
    (k : Names.identifier -> Term.constr) =
  Term.mkNamedLetIn name c t (Term.subst_vars [name] (k name))

let nowhere =
  { Locus.onhyps = Some [];
    Locus.concl_occs = Locus.NoOccurrences
  }

let cps_mk_letin
    (name:string)
    (c: Term.constr)
    (k : Names.identifier  -> Proof_type.tactic)
: Proof_type.tactic =
  fun goal ->
    let name = (Names.id_of_string name) in
    let name =  Tactics.fresh_id [] name goal in
    let letin = (Tactics.letin_tac None  (Names.Name name) c None nowhere) in
    (* let k _ = Tacticals.tclIDTAC  in  *)
    Tacticals.tclTHEN letin (k name) goal

let assert_vector
    (c: Term.constr array) 		(* vector of the types of each sub-goal *)
    subtac
    (k : Names.identifier array -> Proof_type.tactic)
    : Proof_type.tactic =
  let rec aux i l =
    if i = Array.length c
    then k (Array.of_list (List.rev l))
    else
      fun goal ->
	let name = (Names.id_of_string "invert_subgoal") in
	let name =  Tactics.fresh_id [] name goal in
	(* let _ = Format.printf "assert vector subgoal %i: %a\n%!" i pp_constr c.(i) in *)
	let t = (Tactics.assert_tac  (Names.Name name) c.(i)) in
	Tacticals.tclTHENS t
	  [  Tacticals.tclTHEN (Tactics.clear l) subtac;
	    aux (succ i) (name :: l)] goal
  in
  aux 0 []

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


(** The return clause that we builds depends on the shape of the
    telescope [tel]
*)
let filter_return_clause tel sort = 
  Print.(eprint (group (string "telescope" ^^ telescope tel)));
  let rec keep k acc = function 
    | [] -> acc
    | (_,None,ty) as decl :: q -> 
      let realq = q in 
      if not (Term.noccurn k ty) 
      then			  (* k occurs *)
	keep (succ k) (decl :: acc) realq
      else 
	keep (succ k) (Termops.lift_rel_context (-1) acc) realq
    | (_,Some b,ty) as decl :: q -> 
      let realq = q in 
      if not (Term.noccurn k ty)  || not (Term.noccurn k b)
      then			  (* k occurs *)
	keep (succ k) (decl :: acc) (realq)
      else 
	keep (succ k) (Termops.lift_rel_context (-1) acc) realq
  in 
  let result = keep 1 [] tel in 
  Print.(eprint (group (string "result" ^^ telescope result)));
  Term.mkArity (keep 1 [] tel, sort)
  


let debug (st: split_tree list) =
  let open Print in 
  let rec aux = function 
    | None -> string "#"
    | Some (ind, constructor, params, split_trees) ->
      group
	(constr (Term.mkConstruct (ind, constructor)) 
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
    

       
(* replace [Rel 1] with [c] in [stt] *)
let refine_stt c (stt: Telescope.t) = 
  let rec aux n acc = function 
    | [] -> List.rev acc
    | (name,None,ty)::q -> 
      aux (n+1) ((name,None,Term.substnl [c] n ty)::acc) q
  in 
  aux 0 [] stt

let diag2 env sigma (leaf_ids: Names.Id.t list)
    (split_trees: split_tree list) 
    (split_tree_types: Telescope.t)
    (concl: Term.constr)  concl_sort  =

  let rec build env 
      subst shift
      identifier_list
      (stl : split_tree list)
      (stt: Telescope.t)
      =
    Print.(
      let stl = group (string "stl" ^/^ debug stl) in 
      let stt = group (string "stt" ^/^ telescope stt) in 
      let msg = surround 2 2 (string "begin") (stl ^^ hardline ^^ stt) (string "end") in 
      eprint msg
    );
    
    match stl, stt with
    | [], [] -> (* Not dependent inductive *)
      let () = assert (CList.is_empty identifier_list) in
      Print.(eprint (surround_separate_map 2 2 empty (string "substitution:" ^^ lbrace) (break 1) rbrace
		       (fun (i,t) -> group (id i ^/^ string "=>" ^/^ constr t))
		       subst
      ));
      let term = Term.replace_vars subst (Term.lift shift concl) in 
      term
    | ll, ((_,Some _,_) as decl)::stt ->      
      Printf.eprintf "Warning: constructor with let_ins in inversion/build.\n";
      let term = build env subst shift identifier_list stl stt in 
      Term.mkLambda_or_LetIn decl (Term.lift 1 term) 
    | head::ll, ((name_argx,None,ty_argx) as decl) ::stt ->
      let lift_subst = List.map (fun (id, tm) -> (id, Term.lift 1 tm)) subst in
      (* The first thing to do is to introduce the variable we are working on. *)
      Term.mkLambda_or_LetIn decl 
	(
	  match head with 	       
	  | None ->
	    begin match identifier_list with
	    | [] -> Errors.anomaly (Pp.str "build: Less variable than split_tree leaves")
	    |id_h :: id_q ->
	      build env ((id_h, Term.mkRel 1) :: lift_subst) (succ shift) id_q ll stt   
	    end
	  | Some (ind, constructor, params, split_trees) ->
	    (* when we refine a variable, we have to refine its occurences in the [stt] *)
	    let kt i args_ty =
	      let env' = Environ.push_rel_context args_ty env in
	      Print.(eprint (group (string "sub-call: rev-appending" ^/^ rel_context args_ty)));
	      let constr = Term.mkApp (i, Termops.extended_rel_vect 0 args_ty)
	      in 
	      let term =
		build env' 
		  lift_subst (succ shift)
		  identifier_list
		  (split_trees@ll)
		  ((List.rev args_ty)@ refine_stt constr stt )
	      in term
	    in 
	    (* The function that is used to build the term in the non-matching branches of the case *)
	    let kf i args_ty = 
	      let constr = Term.mkApp (i, Termops.extended_rel_vect 0 args_ty) in 
	      Term.it_mkLambda_or_LetIn devil (args_ty @ (refine_stt constr stt)) in  	       
	    let return_clause = 
	      let ind_family = Inductiveops.make_ind_family (ind, params) in
	      let ctx_ind = Inductiveops.make_arity_signature env true ind_family in
	      (* let nhyps = (Term.rel_context_nhyps ctx_ind) in  *)
	      (* let stt =  List.map (Term.map_rel_declaration (Term.lift nhyps)) stt in *)
	      Term.it_mkLambda_or_LetIn
		(filter_return_clause stt concl_sort)
		ctx_ind
	    in
	     mk_matchi env sigma ind constructor params (Term.mkRel 1) return_clause kt kf 
	)
  in
  build env  [] 0 leaf_ids  split_trees split_tree_types 

    
(** Debug version, that only try to construct the diag *)
let pose_diag h name gl = 
  let env = Tacmach.pf_env gl in
  let sigma = Tacmach.project gl in
  let h_ty = Tacmach.pf_get_hyp_typ gl h in

  (** ensures that the name x is fresh in the _first_ goal *)
  let (!!) x = Tactics.fresh_id [] ((Names.id_of_string x)) gl in
  (* get the name of the inductive and the list of arguments it is applied to *)
  let (ind_family, real_args) =
    Inductiveops.dest_ind_type (Inductiveops.find_rectype env sigma h_ty) in
  let (ctx,sort_family) = Inductiveops.get_arity env ind_family in
  let constructors = Inductiveops.get_constructors env ind_family in
  let (split_trees,leaves) = make_a_pattern env sigma (real_args @ [(* Term.mkVar h *)]) in
  let (leaves_ids,generalized_hyps,concl) = prepare_conclusion_type gl leaves in
  let diag =
    diag2 env sigma leaves_ids split_trees (List.rev ctx)  concl (Termops.new_sort_in_family sort_family) 
  in
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
  let (ctx,sort_family) = Inductiveops.get_arity env ind_family in
  let constructors = Inductiveops.get_constructors env ind_family in
  let (split_trees,leaves) = make_a_pattern env sigma (real_args @ [(* Term.mkVar h *)]) in
    (* List.iter (function *)
    (* | LVar v -> Format.eprintf "variable %a\n" pp_constr (Term.mkVar v) *)
    (* | LTerm t -> Format.eprintf "term %a\n" pp_constr t) leaves; *)
    (* Printf.eprintf "\n"; *)
  let (leaves_ids,generalized_hyps,concl) = prepare_conclusion_type gl leaves in
  let diag =
    diag2 env sigma leaves_ids split_trees (List.rev ctx)  concl (Termops.new_sort_in_family sort_family) in
      
  (* Cassons un etage de constructeur de l'inductif *)
let branches diag =
  Array.map
    (fun c ->
      let ctx =  c.Inductiveops.cs_args  in
      let concl_ty = Termops.it_mkProd_or_LetIn
	(
	  let t = Term.mkApp (diag, c.Inductiveops.cs_concl_realargs) in
	    (* DEL: let t = Term.mkApp (t, [| Inductiveops.build_dependent_constructor c |]) in *)
	  t
	)
	ctx
      in
      let body subgoal =
	let x =
	  Namegen.it_mkLambda_or_LetIn_name env
	      (Term.mkApp (subgoal, Termops.extended_rel_vect 0 ctx))
	      ctx
	  in
	  x
	in
	(concl_ty, body)
      )
      constructors
  in
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
	      (* This is a tricky bit of code. The [ctx] value must be
		 an arity like e.g., [n:nat; H:even n], because of the
		 "as" clause of match. Nevertheless, the diag term does
		 not require this extra argument: hence, we recompute
		 the arity without the last element [ctx'], and use it
		 to build the application. *)
	    let ctx = (Inductiveops.make_arity_signature env true ind_family) in
	    let ctx' = (Inductiveops.make_arity_signature env false ind_family) in
	    Term.it_mkLambda_or_LetIn
	      (Term.mkApp (Term.mkVar diag, Termops.extended_rel_vect 1 ctx'))
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


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
  

let filter_return_clause tel sort= 
  Term.mkArity (List.rev tel, sort)

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
    
       
(* replace [Rel 1] with [c] in [stt] and lifts other de Bruijn indices
   by [k].  *)
let refine_stt c k (stt: Telescope.t) = 
  let rec aux n acc = function 
    | [] -> List.rev acc
    | (name,None,ty)::q -> 
      (* let t = foobar c (n+1) 0 ty in  *)
      let t' = Term.substnl [c] n (Term.liftn (k+1) (n+2) ty)  in 
      aux (n+1) ((name,None,t') ::acc) q
  in 
  let result = aux 0 [] stt in 
  Print.(eprint (

    prefix 2 2 (string "refine_stt")
      (messages 
	 [
	   "c", constr' [] c;
	   "stt", telescope stt;
	   "result", telescope result;
	 ])
  ));
  result

let rev_append ctx stt = 
  let result = 
    (* List.rev_append ctx (Telescope.lift (Term.rel_context_nhyps ctx) stt) *)
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



(* replace [c] with [Rel k] in [ctx] *)
let rec anti_subst_rel_context c k ctx = 
  match ctx with 
    | [] -> []
    | (name,None,ty)::ctx -> (name, None, Termops.replace_term c (Term.mkRel k) ty) :: anti_subst_rel_context (Term.lift 1 c) (succ k) ctx
;;

let anti_subst_rel_context c k ctx =
  let r = anti_subst_rel_context c k ctx in
  Print.(eprint 
	   ((string "anti_subst_rel_context") ^//^
	       messages [ "c", constr c;
			  "k", int k;
			  "ctx", rel_context ctx; 
			  "result", rel_context r])
	   
  );
  r


(* We have to iterate the previous function for each argument *)
let rec iter args n ctx = 
  match args with 
    | [] -> ctx
    | t::q -> iter q (succ n) (anti_subst_rel_context t n ctx)


let diag env sigma (leaf_ids: Names.Id.t list)
    (split_trees: split_tree list) 
    (split_tree_types: Telescope.t)
    (concl: Term.constr)  concl_sort  =

  let rec build env 
      subst 
      shift
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
		    build env ((id_h, Term.mkRel 1) :: lift_subst) (succ shift) id_q ll stt   
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
		
		let ind_args = try  Array.to_list (snd (Term.destApp ty_argx)) with _ -> [] in 
		
		let branches =
		  Array.mapi
		    (fun i cs ->
		      (* substitude the matched term (Rel 1) by the constructor in the branch we are *)
		      let args = Inductiveops.build_dependent_constructor cs
			:: Array.to_list cs.Inductiveops.cs_concl_realargs in 
		      let stt = List.rev (Termops.substl_rel_context args (List.rev stt)) in
		      (* let stt = List.rev (iter (args) 1 (List.rev stt)) in 		 *)
		      let branch_body =
			if i + 1 = constructor
			then
			  begin
			    let env' = Environ.push_rel_context cs.Inductiveops.cs_args env in
			    let term =
			      build env' lift_subst 
				(succ shift)
				identifier_list
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
		      branch_body
		    )
		    constructors
		in 
		(* In our running example, args is [S @1] *)
		let return_clause = 
		  let ctx = Inductiveops.make_arity_signature env true ind_family in
		  (* ctx is [vector @1; nat] *)
		  (* stt is [P (S @2) @1]. *)
		  let debug msg f x = 
		    Print.(eprint (group (string msg ^/^ group (f x))))
		  in		  
		  (* We need to lift the arguments by 1, to account for
		     the "in" clause. *)
		  let ind_args = List.map (Term.lift 1) ind_args in 
		  (* Then, we must perform a replacement of the occurences of the
 		     arguments with the variables (this is the dual of a
 		     substitution). *)
		  debug "args" (Print.(separate_map semi constr)) ind_args;
		  debug "ctx" Print.rel_context ctx;
		  debug "stt" Print.telescope stt;
		  
		  let stt = List.rev (iter (Term.mkRel 1::ind_args) 1 (List.rev stt)) in 		
		  (* let stt = List.rev (Termops.substl_rel_context args (List.rev stt)) in *)
 		  debug "stt" Print.telescope stt;
		  let t = filter_return_clause (stt) concl_sort in 
		  debug "t" Print.constr t;
		  let t = Termops.it_mkLambda_or_LetIn t ctx in 
		  t
		in 
		Term.mkCase (case_info,return_clause,Term.mkRel 1,branches)
	  )
  in
  build env  [] 0 leaf_ids  split_trees split_tree_types 


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
  let ctx = Inductiveops.make_arity_signature env true ind_family  in
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
	Print.(eprint (group (string "branches/ctx" ^/^ group (rel_context ctx))));
	let t = Term.mkApp (diag, cs.Inductiveops.cs_concl_realargs) in
	let t = Term.mkApp (t, [| Inductiveops.build_dependent_constructor cs |]) in
	let ty = Term.it_mkProd_or_LetIn t ctx in 
	let body p = p
	in 
	ty, body
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





(* [Rel i] is transformed into
   
   [c] if i = n
   [Rel i] if i < n 
   [Rel i + k] if i > n   
*)
let foobar c n k term = 
  Print.(eprint 
	   (prefix 2 2 (string "foobar") (messages ["c", constr c; "n", int n; "k", int k; "term", constr term])));
  let rec subst depth term = match Term.kind_of_term term with 
    | Term.Rel i when i = n + depth -> Term.lift depth c
    | Term.Rel i when i < n + depth -> term
    | Term.Rel i -> Term.mkRel (i + k) 
    | _ -> Term.map_constr_with_binders succ subst depth term
  in 
  let result = subst 0 term  in 
  Print.(eprint (constr result)); result

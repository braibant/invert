open Invertlib


(* Given an term [term] in type [I params {args}], build a case of return clause
   [return_clause] feeding the impossible branch with a correct term and calling
   [kf] constructor_number constructor_spec expected_type extracted_rel_context
   for others. *)
let mk_casei env sigma ind params term return_clause kf =
  let ind_family = Inductiveops.make_ind_family (ind, params) in
  let case_info = Inductiveops.make_case_info env ind Term.RegularStyle in
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
	Term.lift cs.Inductiveops.cs_nargs return_clause in
      let branch_pre_ty =
	Term.mkApp (lifted_return, cs.Inductiveops.cs_concl_realargs) in
      let branch_ty = Term.mkApp
	(branch_pre_ty, [|Inductiveops.build_dependent_constructor cs|]) in
      let (specialized_ctx,expectation) =
	Reductionops.splay_prod_assum env sigma branch_ty in
      match specialized_ctx with
      | (_,_,ty) :: _
	  when Reductionops.is_conv env sigma ty
	    (Util.delayed_force Coqlib.build_coq_False) ->
	Term.it_mkLambda_or_LetIn
	  (Term.mkApp
	     (Lazy.force false_rect, [|expectation; Term.mkRel 1|]))
	  specialized_ctx
      | _ -> kf i cs branch_ty specialized_ctx
    )
      constructors
  in
  Term.mkCase (case_info,return_clause,term,branches)

let mk_case_tac ind_family term return_clause subtac k = fun gl ->
  let ind = fst (Inductiveops.dest_ind_family ind_family) in
  let env = Tacmach.pf_env gl in
  let sigma = Tacmach.project gl in
  let case_info = Inductiveops.make_case_info env ind Term.RegularStyle in
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
	  Term.lift cs.Inductiveops.cs_nargs return_clause in
	let branch_pre_ty =
	  Term.mkApp (lifted_return, cs.Inductiveops.cs_concl_realargs) in
	let branch_ty = Term.mkApp
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
	      (Term.mkApp
		 (Lazy.force false_rect, [|expectation; Term.mkRel 1|]))
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
		build (succ i) (name :: l) ((Term.mkVar name) :: acc)
	    ] gl
      end
    else
      let term = Term.mkCase (case_info, return_clause, term, (Array.of_list (List.rev acc))) in
      k term gl
  in
  build 0 [] [] gl



let rec split_tree2diag
    env sigma
    (split_trees: Term.constr list)
    (return_type: Term.types)
    (concl: Term.constr)
    =
  (* Print.( *)
  (*   let doc = messages *)
  (*     ["stl", ST.pp_tl split_trees; *)
  (*      "return_type", constr return_type; *)
  (*      "concl", constr concl; *)
  (*     ] *)
  (*   in *)
  (*   let msg = surround 2 2 (string "begin") doc (string "end") in *)
  (*   eprint msg *)
  (* ); *)
  match split_trees with
  | [] -> concl
  | head::ll ->        
    let (name_argx,ty_argx,return_type) =
	Term.destProd
	  (Reductionops.whd_betaiotazeta sigma return_type)
    in
    (* The first thing to do is to introduce the variable we are
       working on and do the lift accordingly.

       This variable has type [ty_argx] == [I pi ai].  *)
    Term.mkLambda
      (name_argx,ty_argx,
       (* we lift head, ll and the conclusion to accound for the previous binder *)
       let head = Term.lift 1 head in 
       let ll = List.map (Term.lift 1) ll in 
       let concl = Term.lift 1 concl in

       (* we update the environment to account for the binder *)
       let env = Environ.push_rel (name_argx,None,ty_argx) env in
       
       (* we can now reduce the head *)
       let (hd,tl) = Reductionops.whd_betadeltaiota_stack env sigma head in
       match Term.kind_of_term hd with
       | Term.Var _  | Term.Rel _ when CList.is_empty tl -> 
	 split_tree2diag env sigma
	   (List.map (Termops.replace_term hd (Term.mkRel 1)) ll)
	   return_type
	   (Termops.replace_term hd (Term.mkRel 1) concl)
       | Term.Construct (ind, constructor) ->
	 let params,split_trees = CList.chop (Inductiveops.inductive_nparams ind) tl in
	 let return_clause,args =
	   matched_type2diag env sigma (Term.mkRel 1) (Term.lift 1 ty_argx) return_type
	 in (*we have the return clause *)
	 let real_body i cs branch_ty specialized_ctx =
	   if i + 1 = constructor
	   then (* recursive call *)
	     split_tree2diag env sigma
	       (split_trees@args@ll)
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
	   (mk_casei env sigma ind params (Term.mkRel 1) return_clause real_body)
	   args
      )
and matched_type2diag env sigma (tm: Term.constr) ty pre_concl =
  let (ind_family, real_args) =
    Inductiveops.dest_ind_type (Inductiveops.find_rectype env sigma ty) in
  let (_,sort_family) = Inductiveops.get_arity env ind_family in
  let split_trees = real_args @ [ tm ] in
  let generalized_hyps,concl = prepare_conclusion env pre_concl split_trees  in
  Print.(
    eprint (
      messages ["hyps", separate_map semi constr generalized_hyps;
		"concl", constr concl]
    )
  );
  let sort = Termops.new_sort_in_family sort_family in
  let return_type = Inductiveops.make_arity env true ind_family sort in
  let result = split_tree2diag env sigma split_trees return_type concl in
  (* put the result in eta long form *)
  let ctx = Inductiveops.make_arity_signature env true ind_family in
  let lifted_result = Term.lift (Term.rel_context_length ctx) result in
  let result' =
    Termops.it_mkLambda_or_LetIn
      (Reductionops.whd_beta sigma
	 (Term.mkApp (lifted_result,Termops.extended_rel_vect 0 ctx))) ctx in
  result', generalized_hyps
and prepare_conclusion env concl stl : Term.constr list * Term.constr =
  (* We have to generalize the elements of the context (either de
     Bruijn or vars) whose type [t] is such that there exists an
     element [e] of the stl such that [e] is a subterm of [t].
     
     Note that we cannot consider the [stl] as a pure list of term,
     since, e.g., [S m] would be considered as a whole, while we would
     like to consider  [m]. 
     
     Therefore, we fold on the context, and introduces these
     generalizations. *)
  let rec popl = function 
    | [] -> []
    | hd :: q -> match Term.kind_of_term hd with 
      | Term.Var x -> hd :: popl q
      | Term.Rel i -> if i > 1 then Term.mkRel (i - 1) :: popl q
	else popl q
      | _ -> popl q
  in
  
  let rec fold_rel_context args term n stl = function 
    | [] -> args, term
    | (name, None, ty) :: ctx -> 
      if 
	List.exists (fun t -> Termops.dependent t ty) stl 
	&& not (List.mem (Term.mkRel 1) stl)
      then
	let args = Term.mkRel n :: args in 
	let term = Termops.replace_term (Term.mkRel n) (Term.mkRel 1) (Term.lift 1 term) in 
	fold_rel_context args (Term.mkProd (name, ty,term))  
	  (succ n) 
	  (popl stl)
	  ctx
      else
	fold_rel_context args term (succ n) (popl stl) ctx 
  in 
  let rec fold_named_context args term stl = function 
    | [] -> args, term
    | (name,body,ty) :: ctx ->      
      if 
	(List.exists (fun t -> Termops.dependent t ty) stl )	
	&& not (List.mem (Term.mkVar name) stl)
      then 	
	let term = Termops.replace_term (Term.mkVar name) (Term.mkRel 1) (Term.lift 1 term) in 
	match body with 
	| None -> 
	  fold_named_context (Term.mkVar name :: args) (Term.mkProd (Names.Name name, ty,term))  
	    (popl stl)
	    ctx
	| Some def -> 
	  fold_named_context  args (Term.mkLetIn (Names.Name name, ty, def, term))
	    (popl stl)
	    ctx
      else 
	fold_named_context args term stl ctx
  in 
  let args, term = fold_rel_context   []   concl 1 stl (Environ.rel_context env) in 
  let args', term' = fold_named_context args term    stl (Environ.named_context env) in 
  Print.(
    let doc = 
      messages 
	["concl",constr concl; 
	 "stl", separate_map semi constr stl;
	 "args", separate_map semi constr args;
	 "term", constr term;
	 "args'", separate_map semi constr args';
	 "term'", constr term';
	]
    in 
    eprint (prefix 2 2 (string "prepare") doc)
  );
  args, term 
  
(** Debug version, that only try to construct the diag *)
let pose_diag h name gl =
  let env = Tacmach.pf_env gl in
  let sigma = Tacmach.project gl in
  let h_ty = Tacmach.pf_get_hyp_typ gl h in
  let pre_concl = Tacmach.pf_concl gl in
  (* get the name of the inductive and the list of arguments it is applied to *)
  let diag,_ = matched_type2diag env sigma (Term.mkVar h) h_ty pre_concl in
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
  let diag,l = matched_type2diag env sigma (Term.mkVar h) h_ty pre_concl in
  Print.(eprint (stripes( string "final diag") ^/^ constr diag));
  Print.(
    eprint (
      messages ["clear", separate_map semi constr l]
    )
  );

  (* Each branch is a pair: type of the subgoal, body of the branch *)
  let (ind_family, _) = Inductiveops.dest_ind_type (Inductiveops.find_rectype env sigma h_ty) in

      let subtac =
	   Tactics.clear (h :: (List.fold_left (fun acc x ->
	       match Term.kind_of_term x with
	       | Term.Var n -> n::acc
	       | _ -> acc
	     ) [] l))
      in
      mk_case_tac ind_family (Term.mkVar h) diag subtac
	(
	  fun term ->
	    let term = Term.applistc term l in
	    Tactics.refine term
	) gl


module ST = struct
  type name =
  | Var of Names.Id.t
  | Rel of int

  let name_to_constr = function 
    | Var v -> Term.mkVar v
    | Rel i -> Term.mkRel i 

  let lift_name n = function
    | Var name -> Var name
    | Rel i -> Rel (i + n)

      
  let eq_name = (=)
      
  type t =
  | Constructor of 
      (Names.inductive * int (* constructor number *) *
	 Term.constr list (* params *) * t list)
  | Leaf of name 

  let var v = Leaf (Var v)
  let rel i = Leaf (Rel i)

  let replace_term d e term = match d with 
    | Var name -> Term.replace_vars [name,e] term
    | Rel i    -> Termops.replace_term (Term.mkRel i) e term 

    
  let make env sigma (args: Term.constr list) : t list =
    (* Print.(eprint  *)
    (* 	     (prefix 2 2 (string "args") *)
    (* 	     (separate_map semi constr args))); *)
    let rec aux arg : t  =
      let (hd,tl) = Reductionops.whd_betadeltaiota_stack env sigma arg in
      match Term.kind_of_term hd with
      | Term.Var v when CList.is_empty tl -> var v
      | Term.Rel i when CList.is_empty tl -> rel i
      | Term.Construct (ind, i) ->
	let params,real_args = CList.chop (Inductiveops.inductive_nparams ind) tl in
	let constrs = List.map aux real_args in
	Constructor (ind, i, params, constrs)
      | _ ->
	Print.(eprint (constr hd));
	invalid_arg "todo"
    in
    List.map aux args
      
  let rec replace (d:name) (e:name) = function 
    | Leaf v -> 
      Leaf (if eq_name v d then e else v)
    | Constructor (ind, constructor, params,stl) -> 
      Constructor (ind, constructor, params, List.map (replace d e) stl)

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
	(constr (Term.mkConstruct (ind, constructor))
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

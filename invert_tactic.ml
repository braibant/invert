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
    Print.(eprint 
	     (prefix 2 2 (string "args")
	     (separate_map semi constr args)));
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

let rec split_tree2diag 
    env sigma 
    (split_trees: ST.t list)
    (return_type: Term.types)
    (concl: Term.constr)
    =  
  Print.(
    let doc = messages
      ["stl", ST.pp_tl split_trees;
       "return_type", constr return_type;
       "concl", constr concl;
      ]
    in
    let msg = surround 2 2 (string "begin") doc (string "end") in
    eprint msg
  );
  let split_trees = ST.liftl 1 split_trees in 
  match split_trees with
  | [] -> concl
  | head::ll ->
    let (name_argx,ty_argx,return_type) = 
      try 
	Term.destProd
	  (Reductionops.whd_betaiotazeta sigma return_type) 
      with e -> 	  Print.(eprint (constr return_type)); raise e
    in
    (* The first thing to do is to introduce the variable we are
       working on and do the lift accordingly.
       
       This variable has type [ty_argx] == [I pi ai].  *)
    Term.mkLambda 
      (name_argx,ty_argx,
       let env = Environ.push_rel (name_argx,None,ty_argx) env in
       let concl = Term.lift 1 concl in
       
       match head with
       | ST.Leaf v -> 
	 split_tree2diag env sigma 
	   (List.map (ST.replace v (ST.Rel 1)) ll)
	   return_type
	   (ST.replace_term  v (Term.mkRel 1) concl)	   
       | ST.Constructor (ind, constructor, params, split_trees) ->
	 (* we want to refine in the [constructor] constructor case. *)
	 let ind_family = Inductiveops.make_ind_family (ind, params) in	 
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
	   let result,args = 
	     matched_type2diag env sigma (Term.mkRel 1) (Term.lift 1 ty_argx) return_type 
	   in
	   (* put the result in eta long form *)
	   let ctx = Inductiveops.make_arity_signature env true ind_family in
	   let lifted_result = Term.lift (Term.rel_context_length ctx) result in
	   let result' =
	     Termops.it_mkLambda_or_LetIn
	       (Reductionops.whd_beta sigma
		  (Term.mkApp (lifted_result,Termops.extended_rel_vect 0 ctx))) ctx in
	   result', args 
	 in (*we have the return clause *)
	 let real_body i cs branch_ty specialized_ctx =
	   if i + 1 = constructor
	   then (* recursive call *)
	     split_tree2diag env sigma 
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
	   (mk_casei env sigma ind params (Term.mkRel 1) return_clause real_body)
	   (List.map ST.name_to_constr args)
      )
and matched_type2diag env sigma (tm: Term.constr) ty pre_concl =
  let (ind_family, real_args) =
    Inductiveops.dest_ind_type (Inductiveops.find_rectype env sigma ty) in
  let (_,sort_family) = Inductiveops.get_arity env ind_family in
  let split_trees = ST.make env sigma (real_args @ [ tm ]) in
  let generalized_hyps,concl = prepare_conclusion env pre_concl split_trees  in
  let sort = Termops.new_sort_in_family sort_family in
  let return_type = Inductiveops.make_arity env true ind_family sort in
  (split_tree2diag env sigma split_trees return_type concl), 
  generalized_hyps
and prepare_conclusion env concl stl : ST.name list * Term.constr = 
  let ctx0 = Environ.rel_context env in 
  let ctx1 = Environ.named_context env in 
  
  let rec occurs_check ty vars  = 
    match vars  with 
    | [] -> false
    | ST.Rel i :: vars ->  Termops.dependent (Term.mkRel i) ty || occurs_check ty vars
    | ST.Var v :: vars ->  Termops.dependent (Term.mkVar v) ty || occurs_check ty vars
  in
  (* Fold on a rel-context *)
  let rec fold_ctx ctx vars args term pos add =
    match ctx with
    | [] -> args, term
    | ((name, None, ty) as decl)::q ->
      let vars' = ST.pop_vars vars in
      if occurs_check ty vars'  && not (List.mem (ST.Rel 1) vars') 
      then
  	let args' = ST.Rel pos :: args in
	let term' = Term.lift 1 term in
	let term'' = Termops.replace_term (Term.mkRel (add + 1)) (Term.mkRel 1) term' in
	fold_ctx q vars' args' (Term.mkProd (name, Term.lift pos ty, term'')) (succ pos) (succ add)
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
  	let term' = Term.lift 1 term in
  	let term'' = Termops.replace_term (Term.mkVar id) (Term.mkRel 1) term' in
  	fold_names q vars args' (Term.mkProd (Names.Name id, ty, term''))
      else
  	fold_names q vars args term
    | ((id, Some body, ty) as decl)::q ->
      if occurs_check ty vars && not (List.mem (ST.Var id) vars)
      then
  	let term' = Term.lift 1 term in
  	let term'' = Termops.replace_term (Term.mkVar id) (Term.mkRel 1) term' in
  	fold_names q vars args (Term.mkLetIn (Names.Name id, ty, body, term''))
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
  (* Each branch is a pair: type of the subgoal, body of the branch *)
  let (ind_family, _) =
    Inductiveops.dest_ind_type (Inductiveops.find_rectype env sigma h_ty) in
  
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
	     Tactics.clear (diag :: h :: (List.fold_left (fun acc x -> 
	       match x with 
	       | ST.Var n -> n::acc
	       | _ -> acc
	     ) [] l))
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
	  let term = Term.applistc term (List.map ST.name_to_constr l) in 
	  Tactics.refine term gl
	)
    ) gl



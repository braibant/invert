let pp_constr fmt x = Pp.pp_with fmt (Printer.pr_constr x)
let pp_list pp fmt l = List.iter (fun x -> Format.fprintf fmt "%a; " pp x) l
let pp_list_nl pp fmt l = List.iter (fun x -> Format.fprintf fmt "%a;\n" pp x) l
let pp_constrs fmt l = (pp_list pp_constr) fmt l

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

(* constructs the term fun x => match x with | t => a | _ => b end
   assume that t is in head normal form *)
let rec diag sigma env t (a: Term.constr) b return  = 
  let tty = Typing.type_of env sigma t in 
  let t = Tacred.hnf_constr env sigma t in 
  let _ = Format.printf "diag %a %a %a\n" pp_constr t pp_constr a pp_constr b in
  mk_fun 
    (Names.id_of_string "x")
    tty 
    (fun x -> 
      let (ind, args) = Inductive.find_inductive env tty in 
      let case_info = Inductiveops.make_case_info env ind Term.MatchStyle in 
      (* the type of each constructor *)
      let (branches_type: Term.types array) = Inductiveops.arities_of_constructors env ind in       
      try
	let head_t, args_t =
	  match Term.kind_of_term t with 
	  | Term.App(hd, v) -> 
	    (match Term.kind_of_term hd with 
	    | Term.Construct c' -> c',v      
	    )
	  | Term.Construct c' -> c', [||]
	in 
	let branches = Array.mapi 
	  (fun i ty -> 
	    let (args_ty,concl_ty) = Term.decompose_prod_assum ty in
	    let args_ty' = List.rev args_ty in 
	    if i + 1 = snd head_t 
	    then 
		(* in this case, we continue to match on [t] *)
	      begin 
		let env = (Environ.push_rel_context args_ty env) in 
		  (* we must match each of the arguments of the constructor
		     against the corresponding term in the arguments of t *)
		let rec aux k : Term.constr= 
		  if k = Array.length args_t 
		  then 
		    a
		  else
		    diag sigma env 
		      args_t.(k) 
		      (aux (succ k)) 
		      b
		      return
		in 
		aux 0	      
	      end
	    else 
		(* otherwise, in the underscore case, we return [b] *)
	      Termops.it_mkLambda_or_LetIn (Term.mkApp (b, [| Term.mkVar x |])) args_ty	 	    
	  ) 
	  branches_type
	in
	let return = 
	  let context = 
	    (Names.Anonymous, None, tty) :: 
	      List.map (fun t -> Names.Anonymous, None, Typing.type_of env sigma t) (List.rev args)
	  in 
	  Termops.it_mkLambda_or_LetIn 
	    (
	      return
	    ) context	  
	in Term.mkCase (case_info,return,Term.mkVar x, branches) 
      with 
      | _ -> Term.mkApp (a, [|Term.mkVar x|])
    )
;;
    
    

let invert h gl = 
  let env = Tacmach.pf_env gl in
  let sigma = Tacmach.project gl in 
  let concl = Tacmach.pf_concl gl in 
  let h_ty = Tacmach.pf_get_hyp_typ gl h in 
  
  (** ensures that the name x is fresh in the _first_ goal *)
  let (!!) x = Tactics.fresh_id [] ((Names.id_of_string x)) gl in  
  
  (* get the name of the inductive and the list of arguments it is applied to *)
  let (ind, constr_list) = Inductive.find_inductive env h_ty in 
  (* extra information for the match *)
  let case_info = Inductiveops.make_case_info env ind Term.MatchStyle in 
  
  begin match constr_list with 
  | [t] -> 
    let ind_ty = (Inductiveops.type_of_inductive env ind) in 
    let arity, sort = Term.destArity ind_ty in 
    (* return clause *)
    let return_clause diag = 
      begin 	
	let _ = assert (List.length arity = 1) in	(* for now *)
	let (_,_,args_ty) = List.hd arity in 
	(* the [in] part *)
	mk_fun (!! "args") args_ty
	  (fun args -> 
	    (* the [as] part *)
	    mk_fun (!! "as_x") h_ty
	      (fun x ->
		    (* for instance if the conclusion is [even n] and the
		       inductive is [even n'], we can substitute [n] in the goal with [n']  *)
		Term.mkApp (Term.mkVar diag, [|Term.mkVar args|])
	      )
	  )	
      end    
    in 
    (* an inductive family is an inductive type with its parameters *)
    let ind_family = Inductiveops.make_ind_family (ind, []) in 
    let constructors = Inductiveops.get_constructors env ind_family in 
    
    (* each branch must be presented as \args.term *)
    let sigma = ref sigma in 
    let branches diag =
      Array.map 
	(fun c ->       
	  let open Inductiveops in 
 	  let env = (Environ.push_rel_context c.cs_args env) in 
	  let concl_ty = Term.mkApp (diag, c.cs_concl_realargs) in 
	  let subgoal = Evarutil.e_new_evar sigma env  concl_ty in
	  Termops.it_mkLambda_or_LetIn (Term.mkCast (subgoal, Term.DEFAULTcast,concl_ty)) c.cs_args
	) constructors
	
    in
    (fun gl -> 
	    (* the proof term *)
	    let term = 
	      begin 
		let env = Tacmach.pf_env gl in
		let sigma = Tacmach.project gl in 
		let diag = (diag sigma env t (Term.mkInd ind) (Term.mkInd ind) (Term.mkSort sort)) in    
		let _ = Format.printf "diag : %a\n" pp_constr diag in
		mk_let 
		  (!! "diag") 
		  diag
		  (Typing.type_of env sigma diag)
		  (fun diag -> 	
		    let branches = branches (Term.mkVar diag) in 
		    Array.iter (fun x -> Format.printf "%a\n%!" pp_constr x);
		    Term.mkCase (case_info,
				 return_clause diag, 
				 Term.mkVar h, 
				 branches))
	      end
	    in 
	    (
	      Format.printf "%a\n" pp_constrs constr_list;
	      Format.printf "%a\n%!" pp_constr term;    
	      Tactics.refine term gl
	    )
    ) gl
  
  | _ -> assert false
  end
;;

open Tacmach
open Tacticals
open Tacexpr
open Tacinterp
open Genarg



TACTIC EXTEND invert
| ["invert" ident(h)] ->     [invert h]      
  END;;

let pp_constr fmt x = Pp.pp_with fmt (Printer.pr_constr x)
let pp_list pp fmt l = List.iter (fun x -> Format.fprintf fmt "%a; " pp x) l
let pp_list_nl pp fmt l = List.iter (fun x -> Format.fprintf fmt "%a;\n" pp x) l
let pp_constrs fmt l = (pp_list pp_constr) fmt l

let mk_fun
    (name:Names.identifier)
    (t: Term.constr)
    (k : Names.identifier -> Term.constr) =
  Term.mkNamedLambda name t (Term.subst_vars [name] (k name))


let invert h gl = 
  let env = Tacmach.pf_env gl in
  let concl = Tacmach.pf_concl gl in 
  let h_ty = Tacmach.pf_get_hyp_typ gl h in 
  
  let (!!) x = Tactics.fresh_id [] ((Names.id_of_string x)) gl in  
  
  (* get the name of the inductive and the list of arguments it is applied to *)
  let (ind, constr_list) = Inductive.find_inductive env h_ty in 
  (* extra information for the match *)
  let case_info = Inductiveops.make_case_info env ind Term.MatchStyle in 
  (* return clause: for now, it is just the dummy return clause that
     returns the conclusion of the goal *)
  let (return_clause: Term.constr) = 
    begin 
      mk_fun (!! "args") (Inductiveops.type_of_inductive env ind)
	(fun args -> 
	  mk_fun (!! "as_x") h_ty
	    (fun x ->
	      concl
	    )
	)	
    end    
  in 
  
  (* the type of each constructors *)
  let (branches_type: Term.types array) = Inductiveops.arities_of_constructors env ind in 
  
  (* each branch must be presented as \args.term *)
  let evar_map, branches = 
    let evar_map = ref (Tacmach.project gl) in 
    let branches = Array.map 
      (fun ty ->       
	let (args_ty,concl_ty) = Term.decompose_prod_assum ty in
	let env = Environ.push_rel_context args_ty env in  
	let evar_map', sub_goal = Evarutil.new_evar !evar_map env concl_ty in 
	evar_map := evar_map';
	Termops.it_mkLambda_or_LetIn (sub_goal) args_ty	
      ) branches_type in 
    !evar_map, branches
  in
  Tacticals.tclTHEN
    (Refiner.tclEVARS evar_map)
    (fun gl -> 
      (* the proof term *)
      let term = Term.mkCase (case_info,return_clause, Term.mkVar h, branches) in 
      Format.printf "%a\n" pp_constrs constr_list;
      Format.printf "%a\n%!" pp_constr term;    
      Tactics.refine term gl
    ) gl

open Tacmach
open Tacticals
open Tacexpr
open Tacinterp
open Genarg



TACTIC EXTEND invert
    | ["invert" ident(h)] ->     [invert h]      
      END;;

  
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
  Term.mkNamedLambda name t (Vars.subst_vars [name] (k name))

let mk_let
    (name:Names.identifier)
    (c: Term.constr)
    (t: Term.constr)
    (k : Names.identifier -> Term.constr) =
  Term.mkNamedLetIn name c t (Vars.subst_vars [name] (k name))

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


let devil =
  Term.mkProd
    (Names.Anonymous,
     Util.delayed_force Coqlib.build_coq_False,
     Util.delayed_force Coqlib.build_coq_True)

let false_rect =
  lazy (Coqlib.coq_constant "Invert" ["Init"; "Logic"] "False_rect")

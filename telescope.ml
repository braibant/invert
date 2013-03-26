
type t = Term.rel_context

(** Checks whether the rel_context [ctx] depends on the de Bruijn
    variable [k] *)
let depends_on k ctx = 
  let rec fold k ctx = 
    match ctx with 
    | [] -> false
    | (_,None,t) :: ctx -> not (Term.noccurn k t) || fold (succ k) ctx
    | (_,Some b,t) :: ctx -> 
      not (Term.noccurn k t) 
      || not (Term.noccurn k b) 
      || fold (succ k) ctx
  in 
  fold k ctx

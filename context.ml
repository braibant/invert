(** A context is a list with the most recent binder first *)
type t = Term.rel_context

(** Checks whether the rel_context [ctx] depends on the de Bruijn
    variable [k] *)
let depends_on k ctx = 
  let rec fold k ctx = 
    match ctx with 
    | [] -> false
    | (_,None,t) :: ctx -> not (Term.noccurn k t) || fold (pred k) ctx
    | (_,Some b,t) :: ctx -> 
      not (Term.noccurn k t) 
      || not (Term.noccurn k b) 
      || fold (pred k) ctx
  in 
  fold (k + List.length ctx) ctx

(** Given a rel_context, filter_deps keeps only the elements that are
    used dependently *)
let filter_deps ctx = 
  let rec aux ctx rctx = 
    match rctx with 
    | [] -> List.rev rctx
    | t :: q -> 
      if depends_on 1 q 
      then aux q (t :: ctx)
      else aux (Termops.lift_rel_context (-1) q) ctx
  in 
  aux ctx []

(** Conversion back to the [rel_context] type *)
external to_rel_context: t -> Term.rel_context = "%identity"

let append (c1 : t) (c2 : t) = 
  List.append c1 c2


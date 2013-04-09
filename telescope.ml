
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

let filter_deps tel = 
  List.rev (Context.filter_deps (List.rev tel))

let to_rel_context x = 
  List.rev x
  
let rec lift n = function 
  | [] -> []
  | (name,body,ty) :: tail -> (name, Option.map (Term.lift n) body, Term.lift n ty) :: lift (succ n) tail

    
  

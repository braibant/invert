
type t = Context.rel_context

(** Checks whether the rel_context [ctx] depends on the de Bruijn
    variable [k] *)
let depends_on k ctx =
  let rec fold k ctx =
    match ctx with
    | [] -> false
    | (_,None,t) :: ctx -> not (Vars.noccurn k t) || fold (succ k) ctx
    | (_,Some b,t) :: ctx ->
      not (Vars.noccurn k t)
      || not (Vars.noccurn k b)
      || fold (succ k) ctx
  in
  fold k ctx

let to_rel_context x =
  List.rev x

let lift n tele =
  List.rev (Termops.lift_rel_context n (List.rev tele ))

(* lift all de Bruijn indices above or equal to [k] by [n] *)
let lift_above k n tele =
  let rec aux k = function
    | [] -> []
    | decl :: q ->
      Context.map_rel_declaration (Vars.liftn n k) decl :: aux (succ k) q
  in
  aux k tele

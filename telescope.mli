(** Data-type for telescopes: that is, lists of binders, with the most
    recent binder being the last one in the list *)
type t = Term.rel_context

val depends_on : int -> t -> bool

(** Data-type for telescopes: that is, lists of binders, with the most
    recent binder being the last one in the list *)
type t = Term.rel_context

val depends_on : int -> t -> bool
val to_rel_context: t -> Term.rel_context
val filter_deps : t -> t
val lift: int -> t -> t

(** lift all de Bruijn indices above or equal to [k] by [n] *)
val lift_above: int -> int -> t -> t

(** A context is a list with the most recent binder first *)
type t = Term.rel_context

(** Checks whether the rel_context [ctx] depends on the de Bruijn
    variable [k] *)
val depends_on: int -> t -> bool

(** Given a rel_context, filter_deps keeps only the elements that are
    used dependently *)
val filter_deps: t -> t

val to_rel_context: t -> Term.rel_context

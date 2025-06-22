(** The evaluator module is responsible for evaluating terms in the context of a
    given environment. *)

val eval : Core.term -> Env.env -> Core.term

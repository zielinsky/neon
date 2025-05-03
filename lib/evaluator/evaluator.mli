(** The evaluator module is responsible for evaluating terms in the context of a
    given environment. *)

val eval : Ast.term -> Env.termEnv -> Ast.term

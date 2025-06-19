val check_totality :
  Core.Var.t -> Core.Var.t -> int -> Core.term -> Env.internal -> unit

val check_strict_positivity :
  ?isPositive:bool -> Core.Var.t -> Core.term -> bool

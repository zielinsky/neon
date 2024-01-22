type var = int
type env
type term = 
  | Type
  | Kind
  | Var of string * var
  | Lambda of string * var * tp * term
  | Product of string * var * tp * tp
  | App of term * term
  | Hole of string * tp 
  | Let of string * var * term * tp * term
and tp = term

val infer_type : env -> Ast.term -> term * term
val check_type : env -> Ast.term -> term -> term
val create_env : unit -> env 
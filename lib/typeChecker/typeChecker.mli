type var = int
type env
type term = 
  | Type
  | Kind
  | Var of string * var
  | Lambda of string * var * term * term
  | Product of string * var * term * term
  | App of term * term

val infer_type : env -> Ast.term -> term * term
val check_type : env -> Ast.term -> term -> term
val create_env : unit -> env 
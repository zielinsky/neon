(* The term list in Neu is stored in reverse order. *)
type whnf =
  | Type
  | Kind
  | Neu of string * Ast.Var.t * Ast.term list
  | Neu_with_Hole of string * Ast.tp * Ast.term list
  | IntType
  | StringType
  | BoolType
  | IntLit of int
  | StringLit of string
  | BoolLit of bool
  | Lambda of string * Ast.Var.t * Ast.tp * Ast.term
  | Product of string * Ast.Var.t * Ast.tp * Ast.tp
  | Case of whnf * Ast.matchPat list

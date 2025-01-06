open Ast
open Env
open ParserAst

val infer_type : env -> uTerm -> term * term
val check_type : env -> uTerm -> term -> term
val eval : term -> termEnv -> term
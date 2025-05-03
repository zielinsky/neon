open Ast
open Env
open ParserAst
module VarMap : Map.S with type key = int

type sub_map = term VarMap.t

val infer_type : env -> uTerm -> term * term
val check_type : env -> uTerm -> term -> term
val substitute : term -> sub_map -> term
val to_whnf : term -> termEnv -> whnf

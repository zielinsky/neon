(* This module provides the type checking and inference for the language. *)
module VarMap : Map.S with type key = int

type sub_map = Ast.term VarMap.t

val infer_type : Env.env -> ParserAst.uTerm -> Ast.term * Ast.tp
val check_type : Env.env -> ParserAst.uTerm -> Ast.term -> Ast.tp
val substitute : Ast.term -> sub_map -> Ast.term
val to_whnf : Ast.term -> Env.termEnv -> Whnf.whnf

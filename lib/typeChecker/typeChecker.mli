(* This module provides the type checking and inference for the language. *)

val infer_type : Env.env -> ParserAst.uTerm -> Ast.term * Ast.tp
val check_type : Env.env -> ParserAst.uTerm -> Ast.term -> Ast.tp
val substitute : Ast.term -> Ast.sub_map -> Ast.term
val to_whnf : Ast.term -> Env.termEnv -> Whnf.whnf

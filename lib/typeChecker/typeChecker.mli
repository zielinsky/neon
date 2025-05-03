(* This module provides the type checking and inference for the language. *)

module Substitution = Substitution
module Whnf = Whnf

val infer_type : Env.env -> ParserAst.uTerm -> Ast.term * Ast.tp
val check_type : Env.env -> ParserAst.uTerm -> Ast.term -> Ast.tp

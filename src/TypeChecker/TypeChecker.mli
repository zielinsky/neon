(* This module provides the type checking and inference for the language. *)

module Substitution = Substitution
module Whnf = Whnf
module Equiv = Equiv

val infer_type : Env.env -> Raw.term -> Core.term * Core.tp
val check_type : Env.env -> Raw.term -> Core.term -> Core.tp

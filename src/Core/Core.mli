type typeCName
type dataCName

module Var : sig
  type t

  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
  val of_int : int -> t
  val to_int : t -> int
  val to_string : t -> string
end

type term =
  | Type
  | Kind
  | Var of string * Var.t
  | IntType
  | StringType
  | BoolType
  | IntLit of int
  | StringLit of string
  | BoolLit of bool
  | Lambda of string * Var.t * tp * term
  | Product of string * Var.t * tp * tp
  | App of term * term
  | Hole of string * tp
  | Let of string * Var.t * term * tp * term
  | TypeArrow of tp * tp
  | Case of term * matchPat list

and constructorDef = { cname : string; telescope : telescope }
and telescope = Empty | Cons of string * Var.t * tp * telescope
and matchPat = pattern * term
and pattern = PatWild | PatCon of dataCName * (string * Var.t) list
and tp = term

(* The term list in Neu is stored in reverse order. *)
type whnf =
  | Type
  | Kind
  | Neu of string * Var.t * term list
  | Neu_with_Hole of string * tp * term list
  | IntType
  | StringType
  | BoolType
  | IntLit of int
  | StringLit of string
  | BoolLit of bool
  | Lambda of string * Var.t * tp * term
  | Product of string * Var.t * tp * tp
  | Case of whnf * matchPat list

val dataCName_of_string : string -> dataCName
val typeCName_of_string : string -> typeCName
val dataCName_to_string : dataCName -> string
val typeCName_to_string : typeCName -> string

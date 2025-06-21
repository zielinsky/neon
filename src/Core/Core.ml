type typeCName = string
type dataCName = string

module Var : sig
  type t

  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
  val of_int : int -> t
  val to_int : t -> int
  val to_string : t -> string
  val dummy_var : t
end = struct
  type t = int

  let compare = Int.compare
  let equal = Int.equal
  let hash = Int.hash
  let to_string = Int.to_string
  let of_int x = x
  let to_int x = x
  let dummy_var = -1
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
  | Case of term * tp * (string * Var.t) option * tp * branch list
  | IfExpr of term * term * term
  | EqType of term * term * tp
  | Refl of term * tp
  | Subst of string * Var.t * tp * term * term * term
  | FixDef of
      string
      * Var.t
      * (string * Var.t * tp) list
      * string
      * Var.t
      * tp
      * tp
      * term

and constructor_def = { cname : string; telescope : telescope }
and telescope = Empty | Cons of string * Var.t * tp * telescope
and branch = pattern * term
and pattern = PatWild | PatCon of dataCName * (string * Var.t * tp) list
and tp = term

type whnf =
  | Type
  | Kind
  (* The term list is stored in reverse order. *)
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
  | Case of term * tp * (string * Var.t) option * tp * branch list
  | IfExpr of whnf * term * term
  | EqType of term * term * tp
  | Refl of term * tp
  | Subst of string * Var.t * tp * term * term * term
  | FixNeu of
      string
      * Var.t
      * (string * Var.t * tp) list
      * string
      * Var.t
      * tp
      * tp
      * term
      * term list

let dataCName_of_string (s : string) : dataCName = s
let typeCName_of_string (s : string) : typeCName = s
let dataCName_to_string (s : dataCName) : string = s
let typeCName_to_string (s : typeCName) : string = s

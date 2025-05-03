type var = int
type typeCName = string
type dataCName = string

type term =
  | Type
  | Kind
  | Var of string * var
  | IntType
  | StringType
  | BoolType
  | IntLit of int
  | StringLit of string
  | BoolLit of bool
  | Lambda of string * var * tp * term
  | Product of string * var * tp * tp
  | App of term * term
  | Hole of string * tp
  | Let of string * var * term * tp * term
  | TypeArrow of tp * tp
  | Case of term * matchPat list

and constructorDef = { cname : string; telescope : telescope }
and telescope = Empty | Cons of string * var * tp * telescope
and matchPat = pattern * term
and pattern = PatWild | PatCon of dataCName * (string * var) list
and tp = term

(* The term list in Neu is stored in reverse order. *)
type whnf =
  | Type
  | Kind
  | Neu of string * var * term list
  | Neu_with_Hole of string * tp * term list
  | IntType
  | StringType
  | BoolType
  | IntLit of int
  | StringLit of string
  | BoolLit of bool
  | Lambda of string * var * tp * term
  | Product of string * var * tp * tp
  | Case of whnf * matchPat list

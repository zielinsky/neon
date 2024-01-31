(* TERMS *)
type var = int

type term =
  | Type
  | Kind
  | Triangle
  | Var of string * var
  | Lambda of string * var * tp * term
  | Product of string * var * tp * tp
  | App of term * term
  | Hole of string * tp
  | Let of string * var * term * tp * term
  | TypeArrow of tp * tp

and tp = term

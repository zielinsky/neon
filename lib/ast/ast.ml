(* TERMS *)
type var = int

type term =
  | Type
  | Kind
  | Var of string * var
  | Lambda of string * var * tp * term
  | Product of string * var * tp * tp
  | App of term * term
  | Hole of string * tp
  | Let of string * var * term * tp * term
  | TypeArrow of tp * tp

and tp = term

(* The term list in Neu constructor is kept in reverse order *)
type whnf =
  | Type
  | Kind
  | Neu of var * term list
  | Neu_with_Hole of string * tp * term list
  | Lambda of var * tp * term
  | Product of var * tp * tp

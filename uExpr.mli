type term = 
  | Prop
  | Type
  | Var of string
  | Lambda of string * term option * term
  | Product of string * term * term
  | App of term * term
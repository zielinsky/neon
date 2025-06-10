type position = { start : Lexing.position; length : int }
type 'a node = { pos : position; data : 'a }
type typeCName = string
type dataCName = string

type term = term_data node

and term_data =
  | Type
  | Kind
  | IntType
  | StringType
  | BoolType
  | IntLit of int
  | StringLit of string
  | BoolLit of bool
  | Var of string
  | Lambda of string * term option * term
  | Product of string * term * term
  | App of term * term
  | TermWithTypeAnno of term * term
  | Let of string * term * term
  | LetDef of string * term
  | Lemma of string * term * term
  | LemmaDef of string * term
  | Hole of string
  | TypeArrow of term * term
  | ADTSig of typeCName * telescope
  | ADTDecl of typeCName * telescope * constructor_def list
  | Case of term * string option * term option * branch list
  | IfExpr of term * term * term
  | EqType of term * term * term
  | Refl of term * term
  | Subst of string * term * term * term

and constructor_def = { cname : dataCName; telescope : telescope }
and telescope = Empty | Cons of string * term * telescope
and branch = pattern * term
and pattern = PatWild | PatCon of dataCName * string list

type program = term list

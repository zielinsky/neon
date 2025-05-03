type position = { start : Lexing.position; length : int }
type 'a node = { pos : position; data : 'a }

type adtCName = string
type typeCName = string
type dataCName = string

type uTerm = term_data node

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
  | Lambda of string * uTerm option * uTerm
  | Product of string * uTerm * uTerm
  | App of uTerm * uTerm
  | TermWithTypeAnno of uTerm * uTerm
  | Let of string * uTerm * uTerm
  | LetDef of string * uTerm
  | Lemma of string * uTerm * uTerm
  | LemmaDef of string * uTerm
  | Hole of string
  | TypeArrow of uTerm * uTerm
  | ADTSig of typeCName * telescope
  | ADTDecl of typeCName * telescope * constructorDef list
  | Case of uTerm * matchPat list

and constructorDef = {
  cname : dataCName;
  telescope : telescope;
}

and telescope =
  | Empty
  | Cons of string * uTerm * telescope

and matchPat = pattern * uTerm

and pattern = 
  | PatWild
  | PatCon of dataCName * string list

type program = uTerm list

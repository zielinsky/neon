type position =
  { start  : Lexing.position
  ; length : int
  }

type 'a node =
  { pos  : position
  ; data : 'a
  }

type uTerm = term_data node
and term_data =
| Type
| Kind
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

type program = uTerm list



type position =
  { start  : Lexing.position
  ; length : int
  }

type 'a node =
  { pos  : position
  ; data : 'a
  }

type term = term_data node
and term_data =
| Type
| Kind
| Var of string
| Lambda of string * term option * term
| Product of string * term * term
| App of term * term
| TermWithTypeAnno of term * term
| Let of string * term * term
| Lemma of string * term * term
| Hole of string

type program = term list

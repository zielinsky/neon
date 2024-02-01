open Ast
open ParserAst

val term_to_string : term -> string
val uterm_to_string : uTerm -> string
val whnf_to_string : whnf -> string
val print : term * tp -> unit

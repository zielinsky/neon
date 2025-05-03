val term_to_string : Ast.term -> string
val uterm_to_string : ParserAst.uTerm -> string
val whnf_to_string : Whnf.whnf -> string
val print : Ast.term * Ast.tp -> unit
val print_def : ParserAst.uTerm -> unit
val pattern_to_string : Ast.pattern -> string
val telescope_to_string : Ast.telescope -> string

{

let raise_error (lexbuf : Lexing.lexbuf) reason =
  let pos =
    { Ast.start  = lexbuf.lex_start_p
    ; Ast.length = lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_start_p.pos_cnum
    }
  in raise (Errors.Parse_error(pos, reason))

}

let whitespace = ['\011'-'\r' '\t' ' ']
let var_start = ['A'-'Z' '_']
let lower     = ['a'-'z']
let var_char  = var_start | lower

rule token = parse
    whitespace+ { token lexbuf }  (* Skip whitespace *)
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | "/*" { block_comment lexbuf;   token lexbuf }
  | '('  { YaccParser.BR_OPN    }
  | ')'  { YaccParser.BR_CLS    }
  | ':'  { YaccParser.COLON     }
  | '='  { YaccParser.EQUAL     }
  | "in"  { YaccParser.IN     }
  | "->" { YaccParser.ARROW     }
  | "type" { YaccParser.TYPE }
  | "kind" { YaccParser.KIND }
  | "fun" { YaccParser.LAMBDA }
  | "pi" { YaccParser.PRODUCT }
  | "let" { YaccParser.LET }
  | "lemma" { YaccParser.LEMMA }
  | var_start var_char* as x { YaccParser.VAR x }
  | eof    { YaccParser.EOF }
  | _ as x {
      raise_error lexbuf (InvalidChar x)
    }

and block_comment = parse
    '\n' { Lexing.new_line lexbuf; block_comment lexbuf }
  | "*/" { () }
  | eof  {
      raise_error lexbuf EofInComment
    }
  | [^'\n' '*']+ { block_comment lexbuf }
  | '*'          { block_comment lexbuf }

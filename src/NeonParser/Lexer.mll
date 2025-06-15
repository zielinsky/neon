{

let raise_error (lexbuf : Lexing.lexbuf) reason =
  let pos =
    { Raw.start  = lexbuf.lex_start_p
    ; Raw.length = lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_start_p.pos_cnum
    }
  in raise (Error.Parse_error(pos, reason))

}

let whitespace = ['\011'-'\r' '\t' ' ']
let var_start = ['a'-'z' '_']
let con_start = ['A' - 'Z']
let var_char = ['a'-'z' 'A'-'Z' '_' '\'' '0'-'9']
let op_char = ['!' '$' '%' '&' '*' '+' '-' '/' ':' '<' '>' '?' '@' '^' '|' '~' '#' '=']

rule token = parse
    whitespace+ { token lexbuf }  (* Skip whitespace *)
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | "/*" { block_comment lexbuf;   token lexbuf }
  | '('  { YaccParser.BR_OPN    }
  | ')'  { YaccParser.BR_CLS    }
  | '{'  { YaccParser.BR_OPN2    }
  | '}'  { YaccParser.BR_CLS2    }
  | ':' '>'  { YaccParser.EQUALTYPE     }
  | ':'  { YaccParser.COLON     }
  | ':'  { YaccParser.COLON     }
  | "==" { YaccParser.EQUALITY }
  | '='  { YaccParser.EQUAL     }
  | ','  { YaccParser.COMMA     }
  | "in"  { YaccParser.IN     }
  | "=>" { YaccParser.ARROW     }
  | "refl" { YaccParser.REFLTYPE }
  | "subst" { YaccParser.SUBST }
  | "." { YaccParser.DOT }
  | "using" { YaccParser.USING }
  | "->" { YaccParser.TYPE_ARROW }
  | "Type" { YaccParser.TYPE }
  | "Kind" { YaccParser.KIND }
  | "fun" { YaccParser.LAMBDA }
  | "forall" { YaccParser.PRODUCT }
  | "fix" { YaccParser.FIX }
  | "let" { YaccParser.LET }
  | "lemma" { YaccParser.LEMMA }
  | "?" var_char* as x { YaccParser.HOLE x }
  | "Int" { YaccParser.INT_TYPE }
  | "String" { YaccParser.STRING_TYPE }
  | "Bool" { YaccParser.BOOL_TYPE }
  | "true" { YaccParser.BOOL_LIT true }
  | "false" { YaccParser.BOOL_LIT false }
  | "data" { YaccParser.ADTDEF }
  | "match" { YaccParser.MATCH }
  | "with" { YaccParser.WITH }
  | "as" { YaccParser.AS }
  | "return" { YaccParser.RETURN }
  | '|' { YaccParser.BAR }
  | '_' { YaccParser.WILDCARD }
  | "if" { YaccParser.IF }
  | "then" { YaccParser.THEN }
  | "else" { YaccParser.ELSE }
  | var_start var_char* as x { YaccParser.VAR x }
  | con_start as x {
     YaccParser.VAR (String.make 1 x)
     }
  | con_start var_char+ as x { YaccParser.ADTCON x }
  (* Integer literals *)
  | ['0'-'9']+ as digits {
      let n = int_of_string digits in
      YaccParser.INT_LIT n
    }
  (* String literals *)
  | '"' [^'"']* '"' as strlit {
      let content_len = String.length strlit - 2 in
      let content     = String.sub strlit 1 content_len in
      YaccParser.STRING_LIT content
    }
  | op_char+ as op {
    YaccParser.OPERATOR op
  }
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

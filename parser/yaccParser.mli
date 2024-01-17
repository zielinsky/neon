type token =
  | TYPE
  | KIND
  | LAMBDA
  | PRODUCT
  | APP
  | TERMWITHYPEANNO
  | LET
  | LEMMA
  | EQUAL
  | IN
  | ARROW
  | VAR of (
# 2 "yaccParser.mly"
       string
# 17 "yaccParser.mli"
)
  | BR_OPN
  | BR_CLS
  | ASTERISK
  | COMMA
  | COLON
  | EOF

val program :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Ast.program

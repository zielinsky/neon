type parser_reason =
| EofInComment
| InvalidNumber   of string
| InvalidChar     of char
| UnexpectedToken of string

exception Parse_error of ParserAst.position * parser_reason

exception Cannot_open_file of
  { fname   : string
  ; message : string
  }

type type_checker_reason = 
| InferTypeError of string * ParserAst.position
| CheckTypeError of string * ParserAst.position
| EqualityError of string
| WhnfError of string

exception Type_error of type_checker_reason
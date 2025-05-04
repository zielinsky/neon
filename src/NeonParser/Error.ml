type parser_reason =
  | EofInComment
  | InvalidNumber of string
  | InvalidChar of char
  | UnexpectedToken of string

exception Parse_error of Raw.position * parser_reason
exception Cannot_open_file of { fname : string; message : string }

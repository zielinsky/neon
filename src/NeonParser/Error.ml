type parser_reason =
  | EofInComment
  | InvalidNumber of string
  | InvalidChar of char
  | UnexpectedToken of string

exception Parse_error of Raw.position * parser_reason
exception Cannot_open_file of { fname : string; message : string }

let reason_to_string (reason : parser_reason) : string =
  match reason with
  | EofInComment -> "EOF in comment"
  | InvalidNumber s -> "Invalid number: " ^ s
  | InvalidChar s -> "Invalid char: " ^ Char.escaped s
  | UnexpectedToken s -> "Unexpected token: " ^ s

let () =
  Printexc.register_printer (function
    | Parse_error (pos, reason) ->
        Some
          (Printf.sprintf "Parse Error at line %d:%d, reason: %s)"
             pos.start.pos_lnum
             (pos.start.pos_cnum - pos.start.pos_bol)
             (reason_to_string reason))
    | _ -> None (* for other exceptions *))

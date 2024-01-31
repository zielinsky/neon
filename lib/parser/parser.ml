type fname = string

let run_parser parse (lexbuf : Lexing.lexbuf) =
  try parse Lexer.token lexbuf
  with Parsing.Parse_error ->
    let pos =
      {
        ParserAst.start = lexbuf.lex_start_p;
        ParserAst.length =
          lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_start_p.pos_cnum;
      }
    in
    raise (Errors.Parse_error (pos, UnexpectedToken (Lexing.lexeme lexbuf)))

let parse_file fname =
  match open_in fname with
  | chan -> (
      match
        let lexbuf = Lexing.from_channel chan in
        lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = fname };
        run_parser YaccParser.program lexbuf
      with
      | result ->
          close_in chan;
          result
      | exception exn ->
          close_in_noerr chan;
          raise exn)
  | exception Sys_error message ->
      raise (Errors.Cannot_open_file { fname; message })

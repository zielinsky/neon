let env = Ast.create_env ()
let term, tp = TypeChecker.infer_type env (List.hd (Parser.parse_file "TestFile"))
let term_s = PrettyPrinter.term_to_string term
let tp_s = PrettyPrinter.term_to_string tp
let _ = print_endline (term_s ^ ": " ^ tp_s)
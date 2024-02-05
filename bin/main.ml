let env = Env.create_env ()

let _ =
  List.iter
    (fun x ->
      PrettyPrinter.print_def x;
      PrettyPrinter.print (TypeChecker.infer_type env x))
    (Parser.parse_file "eq.neon")

(* let term, tp = TypeChecker.infer_type env (List.hd (Parser.parse_file "TestFile.neon"))
   let term_s = PrettyPrinter.term_to_string term
   let tp_s = PrettyPrinter.term_to_string tp
   let _ = print_endline (term_s ^ ": " ^ tp_s) *)

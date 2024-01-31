let env = Env.create_env ()

let print (term, tp) =
  print_endline
    (PrettyPrinter.term_to_string term ^ ": " ^ PrettyPrinter.term_to_string tp)

let _ =
  List.iter (fun x ->  print (TypeChecker.infer_type env x)) (Parser.parse_file "TestFile.neon")
  List.iter
    (fun x -> print (TypeChecker.infer_type env x))
    (Parser.parse_file "TestFile.neon")

(* let term, tp = TypeChecker.infer_type env (List.hd (Parser.parse_file "TestFile.neon"))
   let term_s = PrettyPrinter.term_to_string term
   let tp_s = PrettyPrinter.term_to_string tp
   let _ = print_endline (term_s ^ ": " ^ tp_s) *)
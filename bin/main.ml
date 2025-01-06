open Arg

(* A reference to store the file name provided by the user *)
let file = ref ""

(* A reference to track whether we should print definitions verbosely *)
let verbose_mode = ref false

(* A specification list for possible command line options *)
let speclist = [
  ("-verbose", Set verbose_mode, "Enable verbose printing of definitions");
]

(* Usage message that will be displayed if the user does not provide valid arguments *)
let usage_msg = "Usage: " ^ Sys.argv.(0) ^ " [-verbose] <file>"

let process_parsed_def env x =
  if !verbose_mode then begin
    print_endline "----- PARSED -----";
    PrettyPrinter.print_def x;
    print_endline "-------------------";
  end;

  let (inferred_term, inferred_ty) = TypeChecker.infer_type env x in
  if !verbose_mode then begin
    print_endline "----- INFERRED TYPE -----";
    PrettyPrinter.print (inferred_term, inferred_ty);
    print_endline "-------------------";
  end;

  let nf = TypeChecker.eval inferred_term (snd env) in
  if !verbose_mode then begin
    print_endline "----- NORMAL FORM -----";
    Printf.printf "%s\n\n" (PrettyPrinter.term_to_string nf);
  end

(* The REPL loop. Reads lines, parses them, infers their type, and prints (if verbose). *)
let rec repl env =
  print_string "> ";
  flush stdout;
  match input_line stdin with
  | exception End_of_file ->
      print_endline "Goodbye!";
      exit 0

  | line ->
      if String.trim line = "exit" then (
          print_endline "Goodbye!";
          exit 0
      ) else (
          try
              let parsed = Parser.parse_string line in
              List.iter (fun x -> process_parsed_def env x) parsed
          with
          | Errors.Parse_error _ ->
              let wrapped_line = "let _last = " ^ line in
              let parsed = Parser.parse_string wrapped_line in
              List.iter (fun x -> process_parsed_def env x) parsed
          | ex ->
              Printf.printf "Unexpected error: %s\n" (Printexc.to_string ex);
      );
      repl env

let main () =
(* Parse the command line arguments *)
Arg.parse speclist (fun s -> file := s) usage_msg;

(* Create an empty environment *)
let env = Env.create_env () in

(* If a file is NOT provided, enter REPL mode. *)
if !file = "" then begin
  print_endline "No file specified. Starting REPL mode (type \"exit\" to quit).";
  repl env
end else begin
  (* Otherwise, process the file in batch mode *)
  let parsed = Parser.parse_file !file in
  List.iter (fun x -> process_parsed_def env x) parsed
end

(* Entry point *)
let () = main ()
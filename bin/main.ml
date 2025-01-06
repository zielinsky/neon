open Arg
open Sys
open Filename
open BuiltIn

(* A reference to store the file name provided by the user *)
let file = ref ""

(* A reference to track whether we should print definitions verbosely *)
let verbose_mode = ref false
  
(* A reference to track whether we should load the prelude *)
let load_prelude_mode = ref true

(* A specification list for possible command line options *)
let speclist = [
  ("-verbose", Set verbose_mode, "Enable verbose printing of definitions");
  ("-no-prelude", Clear load_prelude_mode, "Do not load the prelude");
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

  let nf = Evaluator.eval inferred_term (snd env) in
  if !verbose_mode then begin
    print_endline "----- NORMAL FORM -----";
    Printf.printf "%s\n\n" (PrettyPrinter.term_to_string nf);
  end 
  else if not (String.starts_with ~prefix:"_builtin_" (PrettyPrinter.term_to_string nf)) then
    Printf.printf "%s\n%s\n\n" (PrettyPrinter.term_to_string nf) (PrettyPrinter.term_to_string inferred_ty)

(** Recursively lists all .neon files in the given directory. *)
let list_neon_files dir =
  let rec aux acc dirs =
    match dirs with
    | [] -> acc
    | d :: ds ->
        if file_exists d && is_directory d then
          let entries =
            try readdir d |> Array.to_list
            with Sys_error msg ->
              prerr_endline ("Error reading directory " ^ d ^ ": " ^ msg);
              []
          in
          let paths = List.map (fun entry -> concat d entry) entries in
          let files, dirs' = List.partition (fun p -> not (is_directory p)) paths in
          let neon_files = List.filter (fun p -> check_suffix p ".neon") files in
          aux (neon_files @ acc) (dirs' @ ds)
        else
          aux acc ds
  in
  aux [] [dir]

(** Loads all .neon files from the prelude directory into the environment. *)
let load_prelude env prelude_dir =
  if not (file_exists prelude_dir && is_directory prelude_dir) then
    failwith ("Prelude directory not found: " ^ prelude_dir)
  else
    let neon_files = list_neon_files prelude_dir in
    List.iter (fun file ->
        if !verbose_mode then begin
          Printf.printf "Loading prelude file: %s\n%!" file;
        end;
        let parsed = Parser.parse_file file in
        List.iter (fun x -> process_parsed_def env x) parsed
    ) neon_files

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

  (* Load built-in functions into the environment *)
  let _ = load_builtins env in

  (* Load the prelude *)
  if !load_prelude_mode then begin
    let prelude_dir = "stdlib/prelude" in
    load_prelude env prelude_dir
  end;

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
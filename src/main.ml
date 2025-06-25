open Arg
open Sys
open Filename
open BuiltIn

(* A reference to store the file name provided by the user *)
let file = ref ""

(* A reference to track whether we should print definitions verbosely *)
let verbose_mode = ref false
let debug_mode = ref false

(* A reference to track whether we should load the prelude *)
let load_prelude_mode = ref true
let load_builtins_mode = ref true

(* A specification list for possible command line options *)
let speclist =
  [
    ("-verbose", Set verbose_mode, "Enable verbose printing of definitions");
    ("-debug", Set verbose_mode, "Enable debug mode");
    ("-no-prelude", Clear load_prelude_mode, "Do not load the prelude");
    ( "-no-builtin",
      Clear load_builtins_mode,
      "Do not load the built in functions" );
  ]

(* Usage message that will be displayed if the user does not provide valid arguments *)
let usage_msg = "Usage: " ^ Sys.argv.(0) ^ " [params] <file>"

let process_parsed_def env x =
  if !verbose_mode then (
    print_endline "----- PARSED -----";
    PrettyPrinter.print_def x;
    let _ = print_endline "-------------------" in

    let inferred_term, inferred_ty = TypeChecker.infer_type env x in
    print_endline "----- INFERRED TYPE -----";
    PrettyPrinter.print (inferred_term, inferred_ty);
    let _ = print_endline "-------------------" in
    let nf = Evaluator.eval inferred_term env in
    print_endline "----- NORMAL FORM -----";
    if !debug_mode then Printf.printf "%s\n\n" (PrettyPrinter.term_to_string nf)
    else if
      not
        (String.starts_with ~prefix:"(_builtin_"
           (PrettyPrinter.term_to_string nf))
    then Printf.printf "%s\n\n" (PrettyPrinter.term_to_string nf))
  else
    let inferred_term, inferred_ty = TypeChecker.infer_type env x in
    let nf = Evaluator.eval inferred_term env in
    match nf with
    | BoolLit _ | StringLit _ | IntLit _ -> PrettyPrinter.print_def_with_body_and_type x nf inferred_ty
    | _ -> PrettyPrinter.print_def_with_type x inferred_ty

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
          let files, dirs' =
            List.partition (fun p -> not (is_directory p)) paths
          in
          let neon_files =
            List.filter (fun p -> check_suffix p ".neon") files
          in
          aux (neon_files @ acc) (dirs' @ ds)
        else aux acc ds
  in
  aux [] [ dir ]

(** Loads all .neon files from the prelude directory into the environment. *)
let load_prelude env prelude_dir =
  if not (file_exists prelude_dir && is_directory prelude_dir) then
    failwith ("Prelude directory not found: " ^ prelude_dir)
  else
    let neon_files = List.sort String.compare (list_neon_files prelude_dir) in
    List.iter
      (fun file ->
        if !verbose_mode then Printf.printf "Loading prelude file: %s\n%!" file;
        let parsed = NeonParser.Parser.parse_file file in
        List.iter (fun x -> process_parsed_def env x) parsed)
      neon_files

(* The REPL loop. Reads lines, parses them, infers their type, and prints (if verbose). *)
let rec repl env =
  flush stderr;
  print_string "> ";
  flush stdout;
  match input_line stdin with
  | exception End_of_file ->
      print_endline "Goodbye!";
      exit 0
  | line ->
      (if String.trim line = "exit" then (
         print_endline "Goodbye!";
         exit 0)
       else if String.trim line = "env" then
         print_endline (Env.env_to_string env)
       else if String.trim line = "clear" then Sys.command "clear" |> ignore
       else
         try
           let parsed_program = NeonParser.Parser.parse_string line in
           repl_process_parsed_def env parsed_program
         with
         | NeonParser.Error.Parse_error _ as exn -> (
             let wrapped_line = "let _last = " ^ line in
             try
               let parsed_program =
                 NeonParser.Parser.parse_string wrapped_line
               in
               repl_process_parsed_def env parsed_program;
               Env.rm_from_env env "$last"
             with
             | NeonParser.Error.Parse_error _ ->
                 let _ = Printf.eprintf "%s\n" (Printexc.to_string exn) in
                 repl env
             | exn -> Printf.eprintf "%s\n" (Printexc.to_string exn))
         | exn -> Printf.eprintf "%s\n" (Printexc.to_string exn));
      repl env

and repl_process_parsed_def (env : Env.env) (program : Raw.program) : unit =
  let env_copy = Env.copy env in
  try List.iter (fun x -> process_parsed_def env x) program
  with exn ->
    let _ = Printf.eprintf "%s\n" (Printexc.to_string exn) in
    repl env_copy

let main () =
  try
    (* Parse the command line arguments *)
    Arg.parse speclist (fun s -> file := s) usage_msg;

    (* Create an empty environment *)
    let env = Env.create_env () in

    (* Load built-in functions into the environment *)
    if !load_builtins_mode then load_builtins env;

    (* Load the prelude *)
    (if !load_prelude_mode then
       let prelude_dir = "stdlib/prelude" in
       load_prelude env prelude_dir);

    (* If a file is NOT provided, enter REPL mode. *)
    if !file = "" then (
      print_endline
        "No file specified. Starting REPL mode (type \"exit\" to quit).";
      repl env)
    else
      (* Otherwise, process the file in batch mode *)
      let parsed = NeonParser.Parser.parse_file !file in
      List.iter (fun x -> process_parsed_def env x) parsed
  with exn ->
    Printf.eprintf "%s\n" (Printexc.to_string exn);
    exit 1

(* Entry point *)
let () = main ()

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

let main () =
  (* Parse the command line arguments according to speclist.
     Any non-option argument is handled by the anonymous function (fun s -> file := s). *)
  Arg.parse
    speclist
    (fun s -> file := s)
    usage_msg;

  (* Check if a file was provided. If not, print usage and exit. *)
  if !file = "" then begin
    prerr_endline "No file specified. Please provide a file path.";
    Arg.usage speclist usage_msg;
    exit 1
  end;

  (* Create the environment and process the file *)
  let env = Env.create_env () in
  Parser.parse_file !file
  |> List.iter (fun x ->
       (* Only print definitions if verbose mode is enabled *)
       if !verbose_mode then
         PrettyPrinter.print_def x;
       (* Always print the inferred type *)
       PrettyPrinter.print (TypeChecker.infer_type env x)
     )

(* Entry point *)
let () = main ()

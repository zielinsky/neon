open Ast

(* ENV *)
module UTermEnvHashtbl = Hashtbl.Make (String)
module TermEnvHashtbl = Hashtbl.Make (Int)

type env_var = Opaque of tp | Transparent of term * tp
type uTermEnv = var UTermEnvHashtbl.t
type termEnv = env_var TermEnvHashtbl.t
type env = uTermEnv * termEnv

let counter = ref 0

let fresh_var () : int =
  let fresh_var = !counter in
  let _ = counter := !counter + 1 in
  fresh_var

let create_env () : env = (UTermEnvHashtbl.create 10, TermEnvHashtbl.create 10)

let add_to_env ((uTermEnv, termEnv) : env) (nm : string) (var : env_var) : var =
  let y = fresh_var () in
  let _ = UTermEnvHashtbl.add uTermEnv nm y in
  let _ = TermEnvHashtbl.add termEnv y var in
  y

let add_to_termEnv (termEnv : termEnv) (var : var) (env_var : env_var) : unit =
  assert (not (TermEnvHashtbl.mem termEnv var));
  TermEnvHashtbl.add termEnv var env_var

let rm_from_env ((uTermEnv, termEnv) : env) (nm : string) : unit =
  let y = UTermEnvHashtbl.find uTermEnv nm in
  let _ = UTermEnvHashtbl.remove uTermEnv nm in
  TermEnvHashtbl.remove termEnv y

let rm_from_termEnv (termEnv : termEnv) (var : var) : unit =
  TermEnvHashtbl.remove termEnv var

let find_opt_in_env ((uTermEnv, termEnv) : env) (nm : string) :
    (var * env_var) option =
  match UTermEnvHashtbl.find_opt uTermEnv nm with
  | None -> None
  | Some var -> (
      match TermEnvHashtbl.find_opt termEnv var with
      | None -> None
      | Some env_var -> Some (var, env_var))

let find_opt_in_termEnv (termEnv : termEnv) (var : var) : env_var option =
  match TermEnvHashtbl.find_opt termEnv var with
  | None -> None
  | Some env_var -> Some env_var

let env_var_to_string (env_var : env_var option) : string =
  match env_var with
  | None -> "Not found"
  | Some (Opaque tp) -> ": " ^ PrettyPrinter.term_to_string tp
  | Some (Transparent (term, tp)) ->
      "|> " ^ PrettyPrinter.term_to_string term
      ^ " : "
      ^ PrettyPrinter.term_to_string tp

let env_to_string ((uTermEnv, termEnv) : env) : string =
  UTermEnvHashtbl.fold
    (fun key v acc ->
      acc
      ^ Printf.sprintf "%s@%d %s\n" key v
          (env_var_to_string (TermEnvHashtbl.find_opt termEnv v)))
    uTermEnv "\n"
  ^ "\n"

let termEnv_to_string (termEnv : termEnv) : string =
  TermEnvHashtbl.fold
    (fun key v acc ->
      acc ^ Printf.sprintf "%d %s\n" key (env_var_to_string (Some v)))
    termEnv "\n"
  ^ "\n"

(* "x" -> num -> term  *)

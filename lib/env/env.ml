open Ast

(* ENV *)
module StringHashtbl = Hashtbl.Make (String)
module IntHashtbl = Hashtbl.Make (Int)

type env_var = 
  | Opaque of tp 
  | Transparent of term * tp 

type adt_var = 
| AdtTSig of telescope * dataCName list
| AdtDSig of typeCName * telescope

type uTermEnv = var StringHashtbl.t
type termEnv = env_var IntHashtbl.t
type adtEnv = adt_var StringHashtbl.t
type env = uTermEnv * termEnv * adtEnv

let counter = ref 0

let fresh_var () : int =
  let fresh_var = !counter in
  let _ = counter := !counter + 1 in
  fresh_var

let create_env () : env = (StringHashtbl.create 10, IntHashtbl.create 10, StringHashtbl.create 10)

let add_to_env ((uTermEnv, termEnv, _) : env) (nm : string) (var : env_var) : var =
  let y = fresh_var () in
  let _ = StringHashtbl.add uTermEnv nm y in
  let _ = IntHashtbl.add termEnv y var in
  y

let add_to_termEnv (termEnv : termEnv) (var : var) (env_var : env_var) : unit =
  assert (not (IntHashtbl.mem termEnv var));
  IntHashtbl.add termEnv var env_var

let add_to_adtEnv (adtEnv : adtEnv) (nm : string) (adt_var : adt_var) : unit =
  if (StringHashtbl.mem adtEnv nm)
  then failwith "ADT already exists in Env"
  else StringHashtbl.add adtEnv nm adt_var 

(* TODO Think about not using fresh var here *)
let rec add_telescope_to_env ((uTermEnv, termEnv, _) as env: env) (ts : telescope) : unit =
match ts with
  | Empty -> ()
  | Cons (nm, var, tp, ts) -> 
    let _ = StringHashtbl.add uTermEnv nm var in
    let _ = IntHashtbl.add termEnv var (Opaque tp) in
    add_telescope_to_env env ts

let rm_from_env ((uTermEnv, termEnv, _) : env) (nm : string) : unit =
  let y = StringHashtbl.find uTermEnv nm in
  let _ = StringHashtbl.remove uTermEnv nm in
  IntHashtbl.remove termEnv y

let rm_from_termEnv (termEnv : termEnv) (var : var) : unit =
  IntHashtbl.remove termEnv var
  
let rec rm_telescope_from_env (env: env) (ts : telescope) : unit =
match ts with
  | Empty -> ()
  | Cons (nm, _, _, ts) -> 
    let _ = rm_from_env env nm in
    rm_telescope_from_env env ts

let rm_from_adtEnv (adtEnv : adtEnv) (nm : string) : unit =
  StringHashtbl.remove adtEnv nm

let rm_from_uTermEnv (uTermEnv: uTermEnv) (nm: string): unit =
  StringHashtbl.remove uTermEnv nm

let find_opt_in_env ((uTermEnv, termEnv, _) : env) (nm : string) :
    (var * env_var) option =
  match StringHashtbl.find_opt uTermEnv nm with
  | None -> None
  | Some var -> (
      match IntHashtbl.find_opt termEnv var with
      | None -> None
      | Some env_var -> Some (var, env_var))

let find_opt_in_termEnv (termEnv : termEnv) (var : var) : env_var option =
  IntHashtbl.find_opt termEnv var

let find_opt_in_adtEnv (adtEnv : adtEnv) (nm : string) :adt_var option =
  StringHashtbl.find_opt adtEnv nm

let env_var_to_string (env_var : env_var option) : string =
  match env_var with
  | None -> "Not found"
  | Some (Opaque tp) -> ": \x1b[1m" ^ PrettyPrinter.term_to_string tp ^ "\x1b[0m"
  | Some (Transparent (term, tp)) ->
      "|> "
      ^ PrettyPrinter.term_to_string term
      ^ " : \x1b[1m"
      ^ PrettyPrinter.term_to_string tp^ "\x1b[0m"

let env_to_string ((uTermEnv, termEnv, _) : env) : string =
  StringHashtbl.fold
    (fun key v acc ->
      acc
      ^ Printf.sprintf "%s %s\n" key
          (env_var_to_string (IntHashtbl.find_opt termEnv v)))
    uTermEnv "\n"
  ^ "\n"

let termEnv_to_string (termEnv : termEnv) : string =
  IntHashtbl.fold
    (fun key v acc ->
      acc ^ Printf.sprintf "%d %s\n" key (env_var_to_string (Some v)))
    termEnv "\n"
  ^ "\n"

let generate_fresh_var_name (env : env) (nm : string) : string =
  let rec helper ((uTermEnv, _, _) : env) (nm : string) (cnt : int) : string =
    let new_nm = nm ^ "_" ^ Int.to_string cnt in
    if StringHashtbl.mem uTermEnv new_nm then helper env nm (cnt + 1)
    else new_nm
  in
  helper env nm 0

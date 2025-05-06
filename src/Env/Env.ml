module StringHashtbl = Hashtbl.Make (String)
module VarHashtbl = Hashtbl.Make (Core.Var)

type env_var = Opaque of Core.tp | Transparent of Core.term * Core.tp

type adt_var =
  | AdtTSig of Core.telescope * Core.dataCName list
  | AdtDSig of Core.typeCName * Core.telescope

type surface = Core.Var.t StringHashtbl.t
type internal = env_var VarHashtbl.t
type adt = adt_var StringHashtbl.t

type env = {surface: surface; internal: internal; adt: adt}

let counter = ref 0

let fresh_var () : Core.Var.t =
  let fresh_var = !counter in
  let _ = counter := !counter + 1 in
  Core.Var.of_int fresh_var

let create_env () : env =
  {surface = StringHashtbl.create 10; internal = VarHashtbl.create 10; adt = StringHashtbl.create 10}

let add_to_env (env : env) (nm : string) (var : env_var) :
    Core.Var.t =
  let y = fresh_var () in
  let _ = StringHashtbl.add env.surface nm y in
  let _ = VarHashtbl.add env.internal y var in
  y

let add_to_internal_env (env : internal) (var : Core.Var.t) (env_var : env_var) :
    unit =
  assert (not (VarHashtbl.mem env var));
  VarHashtbl.add env var env_var

let add_to_adt_env (env : adt) (nm : string) (adt_var : adt_var) : unit =
  if StringHashtbl.mem env nm then failwith "ADT already exists in Env"
  else StringHashtbl.add env nm adt_var

let rec add_telescope_to_env (env : env)
    (ts : Core.telescope) : unit =
  match ts with
  | Empty -> ()
  | Cons (nm, var, tp, ts) ->
      let _ = StringHashtbl.add env.surface nm var in
      let _ = VarHashtbl.add env.internal var (Opaque tp) in
      add_telescope_to_env env ts

let rm_from_env (env : env) (nm : string) : unit =
  let y = StringHashtbl.find env.surface nm in
  let _ = StringHashtbl.remove env.surface nm in
  VarHashtbl.remove env.internal y

let rm_from_internal_env (env : internal) (var : Core.Var.t) : unit =
  VarHashtbl.remove env var

let rec rm_telescope_from_env (env : env) (ts : Core.telescope) : unit =
  match ts with
  | Empty -> ()
  | Cons (nm, _, _, ts) ->
      let _ = rm_from_env env nm in
      rm_telescope_from_env env ts

let rm_from_adt_env (env : adt) (nm : string) : unit =
  StringHashtbl.remove env nm

let rm_from_surface_env (env : surface) (nm : string) : unit =
  StringHashtbl.remove env nm

let find_opt_in_env (env : env) (nm : string) :
    (Core.Var.t * env_var) option =
  match StringHashtbl.find_opt env.surface nm with
  | None -> None
  | Some var -> (
      match VarHashtbl.find_opt env.internal var with
      | None -> None
      | Some env_var -> Some (var, env_var))

let find_opt_in_internal_env (env : internal) (var : Core.Var.t) : env_var option
    =
  VarHashtbl.find_opt env var

let find_opt_in_adt_env (env : adt) (nm : string) : adt_var option =
  StringHashtbl.find_opt env nm

let env_var_to_string (env_var : env_var option) : string =
  match env_var with
  | None -> "Not found"
  | Some (Opaque tp) ->
      ": \x1b[1m" ^ PrettyPrinter.term_to_string tp ^ "\x1b[0m"
  | Some (Transparent (term, tp)) ->
      "|> "
      ^ PrettyPrinter.term_to_string term
      ^ " : \x1b[1m"
      ^ PrettyPrinter.term_to_string tp
      ^ "\x1b[0m"

let env_to_string (env : env) : string =
  StringHashtbl.fold
    (fun key v acc ->
      acc
      ^ Printf.sprintf "%s %s\n" key
          (env_var_to_string (VarHashtbl.find_opt env.internal v)))
    env.surface "\n"
  ^ "\n"

let internal_env_to_string (env : internal) : string =
  VarHashtbl.fold
    (fun key v acc ->
      acc
      ^ Printf.sprintf "%d %s\n" (Core.Var.to_int key)
          (env_var_to_string (Some v)))
    env "\n"
  ^ "\n"

let generate_fresh_var_name (nm : string) : string =
  let fresh_var = fresh_var () in
  nm ^ "$" ^ Core.Var.to_string fresh_var

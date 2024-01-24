(* TERMS *)
type var = int

type term = 
  | Type
  | Kind
  | Var of string * var
  | Lambda of string * var * tp * term
  | Product of string * var * tp * tp
  | App of term * term
  | Hole of string * tp 
  | Let of string * var * term * tp * term
  | TypeArrow of tp * tp
and tp = term


(* ENV *)
module EnvHashtbl = Hashtbl.Make(String)
type env_var = 
  | Opaque of tp
  | Transparent of term * tp
type env = (var * env_var) EnvHashtbl.t 

let create_env () : env =
  EnvHashtbl.create 10

let add_to_env (env: env) (nm : string) (elem : var * env_var) : unit =
  EnvHashtbl.add env nm elem

let rm_from_env (env: env) (nm : string) : unit =
  EnvHashtbl.remove env nm

let find_opt_in_env (env: env) (nm: string) : (var * env_var) option =
  EnvHashtbl.find_opt env nm
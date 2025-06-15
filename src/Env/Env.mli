type env_var = Opaque of Core.tp | Transparent of Core.term * Core.tp

type adt_var =
  | AdtTSig of Core.telescope * Core.dataCName list
  | AdtDSig of Core.typeCName * Core.telescope

type surface
type internal
type adt
type env = { surface : surface; internal : internal; adt : adt }

val fresh_var : unit -> Core.Var.t
val create_env : unit -> env
val add_to_env : env -> string -> env_var -> Core.Var.t
val add_to_env_with_var : env -> string -> env_var -> Core.Var.t -> Core.Var.t
val add_to_internal_env : internal -> Core.Var.t -> env_var -> unit
val add_to_adt_env : adt -> string -> adt_var -> unit
val add_telescope_to_env : env -> Core.telescope -> unit
val rm_from_env : env -> string -> unit
val rm_from_internal_env : internal -> Core.Var.t -> unit
val rm_telescope_from_env : env -> Core.telescope -> unit
val rm_from_adt_env : adt -> string -> unit
val rm_from_surface_env : surface -> string -> unit
val find_opt_in_env : env -> string -> (Core.Var.t * env_var) option
val find_opt_in_internal_env : internal -> Core.Var.t -> env_var option
val find_opt_in_adt_env : adt -> string -> adt_var option
val env_var_to_string : env_var option -> string
val env_to_string : env -> string
val internal_env_to_string : internal -> string
val generate_fresh_var_name : string -> string
val copy : env -> env

val add_pattern_vars_to_internal_env :
  (string * Core.Var.t) list ->
  Core.term list ->
  internal ->
  (string * Core.Var.t * Core.Var.t) list

val rm_pattern_vars_from_internal_env :
  (string * Core.Var.t * Core.Var.t) list -> internal -> unit

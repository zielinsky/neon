type env_var = Opaque of Core.tp | Transparent of Core.term * Core.tp

type adt_var =
  | AdtTSig of Core.telescope * Core.dataCName list
  | AdtDSig of Core.typeCName * Core.telescope

type uTermEnv
type termEnv
type adtEnv
type env = uTermEnv * termEnv * adtEnv

val fresh_var : unit -> Core.Var.t
val create_env : unit -> env
val add_to_env : env -> string -> env_var -> Core.Var.t
val add_to_termEnv : termEnv -> Core.Var.t -> env_var -> unit
val add_to_adtEnv : adtEnv -> string -> adt_var -> unit
val add_telescope_to_env : env -> Core.telescope -> unit
val rm_from_env : env -> string -> unit
val rm_from_termEnv : termEnv -> Core.Var.t -> unit
val rm_telescope_from_env : env -> Core.telescope -> unit
val rm_from_adtEnv : adtEnv -> string -> unit
val rm_from_uTermEnv : uTermEnv -> string -> unit
val find_opt_in_env : env -> string -> (Core.Var.t * env_var) option
val find_opt_in_termEnv : termEnv -> Core.Var.t -> env_var option
val find_opt_in_adtEnv : adtEnv -> string -> adt_var option
val env_var_to_string : env_var option -> string
val env_to_string : env -> string
val termEnv_to_string : termEnv -> string
val generate_fresh_var_name : env -> string -> string

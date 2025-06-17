type type_checker_reason =
  | InferTypeError of string
  | CheckTypeError of string
  | EqualityError of string
  | WhnfError of string
  | GuardError of string

exception Type_error of type_checker_reason

val create_infer_type_error :
  Raw.position -> string -> Raw.term -> Env.env -> 'a

val create_check_type_error :
  Raw.position -> string -> Raw.term -> Core.tp -> Env.env -> 'a

val create_whnf_error : Core.term -> Env.internal -> string -> 'a
val create_guard_error : string -> Core.term -> 'a

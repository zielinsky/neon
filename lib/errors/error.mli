type parser_reason =
  | EofInComment
  | InvalidNumber of string
  | InvalidChar of char
  | UnexpectedToken of string

exception Parse_error of Raw.position * parser_reason
exception Cannot_open_file of { fname : string; message : string }

type type_checker_reason =
  | InferTypeError of string
  | CheckTypeError of string
  | EqualityError of string
  | WhnfError of string

exception Type_error of type_checker_reason

val create_infer_type_error :
  Raw.position -> string -> Raw.uTerm -> Env.env -> 'a

val create_check_type_error :
  Raw.position -> string -> Raw.uTerm -> Core.tp -> Env.env -> 'a

val create_whnf_error : Core.term -> Env.termEnv -> string -> 'a

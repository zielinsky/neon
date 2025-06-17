type type_checker_reason =
  | InferTypeError of string
  | CheckTypeError of string
  | EqualityError of string
  | WhnfError of string
  | GuardError of string

exception Type_error of type_checker_reason

(** [create_infer_type_error pos error_msg term env] raises a failure exception
    with an error message when an error occurs during type inference of [term].
    It prints detailed information about the term, the error, and the
    environment.

    @param pos The position in the source code where the error occurred.
    @param error_msg A message describing the error.
    @param term The term whose type was being inferred when the error occurred.
    @param env The environment at the time of the error.
    @raise Failure
      Always raises a [Failure] exception with an error message including the
      line and column number. *)
let create_infer_type_error (pos : Raw.position) (error_msg : string)
    (term : Raw.term) (env : Env.env) : 'a =
  let _ =
    print_endline
      ("While inferring the type of term: "
      ^ PrettyPrinter.uterm_to_string term
      ^ "\n\n The following error occurred:\n\t" ^ error_msg ^ "\n"
      ^ "\nThe state of the environment at that moment:\n"
      ^ Env.env_to_string env)
  in
  failwith
    ("Error at line "
    ^ Int.to_string pos.start.pos_lnum
    ^ ":"
    ^ Int.to_string (pos.start.pos_cnum - pos.start.pos_bol))

(** [create_check_type_error pos error_msg term tp env] raises a failure
    exception with an error message when an error occurs during type checking of
    [term] against the expected type [tp]. It prints detailed information about
    the term, the expected type, the error, and the environment.

    @param pos The position in the source code where the error occurred.
    @param error_msg A message describing the error.
    @param term The term that was being type-checked when the error occurred.
    @param tp The expected type of the term.
    @param env The environment at the time of the error.
    @raise Failure
      Always raises a [Failure] exception with an error message including the
      line and column number. *)
let create_check_type_error (pos : Raw.position) (error_msg : string)
    (term : Raw.term) (tp : Core.tp) (env : Env.env) : 'a =
  let _ =
    print_endline
      ("While checking the type of term: "
      ^ PrettyPrinter.uterm_to_string term
      ^ "\nwith expected type: "
      ^ PrettyPrinter.term_to_string tp
      ^ "\n\nThe following error occurred:\n" ^ error_msg ^ "\n"
      ^ "\nThe state of the environment at that moment:\n"
      ^ Env.env_to_string env)
  in
  failwith
    ("Error at line "
    ^ Int.to_string pos.start.pos_lnum
    ^ ":"
    ^ Int.to_string (pos.start.pos_cnum - pos.start.pos_bol))

(** [create_whnf_error term env error_msg] raises a failure exception with an
    error message when an error occurs during the conversion of [term] to its
    weak head normal form (WHNF). It prints detailed information about the term,
    the error, and the environment.

    @param term
      The term that was being converted to WHNF when the error occurred.
    @param env The term environment at the time of the error.
    @param error_msg A message describing the error.
    @raise Failure Always raises a [Failure] exception with an error message. *)
let create_whnf_error (term : Core.term) (env : Env.internal)
    (error_msg : string) : 'a =
  let _ =
    print_endline
      ("While converting term "
      ^ PrettyPrinter.term_to_string term
      ^ "\nto WHNF" ^ "\n\nThe following error occurred:\n\t" ^ error_msg ^ "\n"
      ^ "\nThe state of the environment at that moment:\n"
      ^ Env.internal_env_to_string env)
  in
  failwith "Error when converting to WHNF"

(** [create_guard_error error_msg term] raises a failure exception with an error
    message when an error occurs while checking the guard of a fixpoint. It
    prints detailed information about the term, the error, and the environment.

    @param error_msg A message describing the error.
    @param term The term whose guard was being checked when the error occurred.
    @raise Failure Always raises a [Failure] exception with an error message. *)
let create_guard_error (error_msg : string) (term : Core.term) : 'a =
  let _ =
    print_endline
      ("While checking fixpoint guard: "
      ^ PrettyPrinter.term_to_string term
      ^ "\n\nThe following error occurred:\n\t" ^ error_msg ^ "\n")
  in
  failwith "Error in guard check:"

let () =
  Printexc.register_printer (function
    | Type_error (InferTypeError msg) -> Some ("Type inference error: " ^ msg)
    | Type_error (CheckTypeError msg) -> Some ("Type checking error: " ^ msg)
    | Type_error (EqualityError msg) -> Some ("Type equality error: " ^ msg)
    | Type_error (WhnfError msg) -> Some ("WHNF conversion error: " ^ msg)
    | Type_error (GuardError msg) -> Some ("Guard check error: " ^ msg)
    | _ -> None)

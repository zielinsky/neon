open PrettyPrinter
open Env
module VarMap = Map.Make (Int)

type sub_map = Ast.term VarMap.t

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
let create_infer_type_error (pos : ParserAst.position) (error_msg : string)
    (term : ParserAst.uTerm) (env : env) : 'a =
  let _ =
    print_endline
      ("While inferring the type of term: " ^ uterm_to_string term
     ^ "\n\n The following error occurred:\n\t" ^ error_msg ^ "\n"
     ^ "\nThe state of the environment at that moment:\n" ^ env_to_string env)
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
let create_check_type_error (pos : ParserAst.position) (error_msg : string)
    (term : ParserAst.uTerm) (tp : Ast.tp) (env : env) : 'a =
  let _ =
    print_endline
      ("While checking the type of term: " ^ uterm_to_string term
     ^ "\nwith expected type: " ^ term_to_string tp
     ^ "\n\nThe following error occurred:\n" ^ error_msg ^ "\n"
     ^ "\nThe state of the environment at that moment:\n" ^ env_to_string env)
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
let create_whnf_error (term : Ast.term) (env : termEnv) (error_msg : string) :
    'a =
  let _ =
    print_endline
      ("While converting term " ^ term_to_string term ^ "\nto WHNF"
     ^ "\n\nThe following error occurred:\n\t" ^ error_msg ^ "\n"
     ^ "\nThe state of the environment at that moment:\n"
     ^ termEnv_to_string env)
  in
  failwith "Error when converting to WHNF"

let telescope_length (ts : Ast.telescope) : int =
  let rec tele_len (ts : Ast.telescope) (acc : int) =
    match ts with Empty -> acc | Cons (_, _, _, ts) -> tele_len ts (acc + 1)
  in
  tele_len ts 0

let split_pattern_args (tsT_len : int) (args : string list) :
    string list * string list =
  let rec split_list_at_n (n : int) (xs : 'a list) (acc : 'a list) =
    match (xs, n) with
    | xs, 0 -> (List.rev acc, xs)
    | x :: xs, _ -> split_list_at_n (n - 1) xs (x :: acc)
    | [], _ -> failwith "Unreachable in split_list_at_n"
  in
  let _ = assert (List.length args >= tsT_len) in
  split_list_at_n tsT_len args []

(** [substitute t sub] performs capture-avoiding substitution on term [t] using
    the substitution map [sub]. It replaces variables in [t] according to [sub],
    ensuring that bound variables are correctly handled to prevent variable
    capture.

    @param t The term in which to perform substitution.
    @param sub The substitution map, mapping variable identifiers to terms.
    @return A new term where variables have been substituted according to [sub].
*)
let rec substitute (t : Ast.term) (sub : sub_map) : Ast.term =
  match t with
  | Var (nm, x) -> (
      match VarMap.find_opt x sub with Some t -> t | None -> Var (nm, x))
  | Lambda (nm, x, tp, body) ->
      let y = fresh_var () in
      Lambda
        ( nm,
          y,
          substitute tp sub,
          substitute body (VarMap.add x (Ast.Var (nm, y)) sub) )
  | Product (nm, x, tp, body) ->
      let y = fresh_var () in
      Product
        ( nm,
          y,
          substitute tp sub,
          substitute body (VarMap.add x (Ast.Var (nm, y)) sub) )
  | App (t1, t2) -> App (substitute t1 sub, substitute t2 sub)
  | TypeArrow (t1, t2) -> TypeArrow (substitute t1 sub, substitute t2 sub)
  | Let (nm, x, t, tp_t, body) ->
      let y = fresh_var () in
      Let
        ( nm,
          y,
          substitute t sub,
          substitute tp_t sub,
          substitute body (VarMap.add x (Ast.Var (nm, y)) sub) )
  | Type | Kind | Hole _ | IntType | StringType | BoolType | IntLit _
  | StringLit _ | BoolLit _ ->
      t
  | Case (scrutinee, matchPats) ->
      let scrutinee' = substitute scrutinee sub in
      let matchPats' =
        List.map
          (fun (pattern, t) ->
            match pattern with
            | Ast.PatWild -> (Ast.PatWild, substitute t sub)
            | Ast.PatCon (con_nm, vars) ->
                let sub, rev_vars =
                  List.fold_left
                    (fun (sub_map, new_vars) (nm, var) ->
                      let fresh_var = fresh_var () in
                      ( VarMap.add var (Ast.Var (nm, fresh_var)) sub_map,
                        (nm, fresh_var) :: new_vars ))
                    (sub, []) vars
                in
                (Ast.PatCon (con_nm, List.rev rev_vars), substitute t sub))
          matchPats
      in
      Case (scrutinee', matchPats')

(** [substitute_whnf t sub] performs substitution on a term in weak head normal
    form (WHNF) [t] using the substitution map [sub].

    @param t The WHNF term in which to perform substitution.
    @param sub The substitution map.
    @return A new WHNF term with substitutions applied. *)
let substitute_whnf (t : Whnf.whnf) (sub : sub_map) : Whnf.whnf =
  match t with
  | Type | Kind | IntType | StringType | BoolType | IntLit _ | StringLit _
  | BoolLit _ | Case _ ->
      t
  | Neu (nm, var, term_list) ->
      Neu (nm, var, List.map (fun t -> substitute t sub) term_list)
  | Neu_with_Hole (nm, tp, term_list) ->
      Neu_with_Hole (nm, tp, List.map (fun t -> substitute t sub) term_list)
  | Lambda (nm, var, tp, body) ->
      Lambda (nm, var, substitute tp sub, substitute body sub)
  | Product (nm, var, tp, body) ->
      Product (nm, var, substitute tp sub, substitute body sub)

let rec substitute_in_telescope (ts : Ast.telescope) (sub : sub_map) :
    Ast.telescope =
  match ts with
  | Cons (nm, var, tp, tl) ->
      Cons (nm, var, substitute tp sub, substitute_in_telescope tl sub)
  | Empty -> Empty

(** [to_whnf t env] converts a term [t] to its weak head normal form (WHNF) in
    the context of environment [env].

    @param t The term to convert to WHNF.
    @param env The term environment.
    @return The WHNF form of [t].
    @raise Failure
      If an error occurs during conversion, raises a failure with an appropriate
      error message. *)
let rec to_whnf (t : Ast.term) (env : termEnv) : Whnf.whnf =
  match t with
  | Type ->
      (* 'Type' is already in WHNF *)
      Type
  | Kind ->
      (* 'Kind' is already in WHNF *)
      Kind
  | IntType ->
      (* 'IntType' is already in WHNF *)
      IntType
  | StringType ->
      (* 'StringType' is already in WHNF *)
      StringType
  | BoolType ->
      (* 'BoolType' is already in WHNF *)
      BoolType
  | IntLit n ->
      (* Integer literal is already in WHNF *)
      IntLit n
  | StringLit s ->
      (* String literal is already in WHNF *)
      StringLit s
  | BoolLit s ->
      (* Boolean literal is already in WHNF *)
      BoolLit s
  | Var (nm, x) -> (
      (* Variable 'x' with name 'nm' *)
      match find_opt_in_termEnv env x with
      | Some (Opaque _) ->
          (* Variable is opaque (e.g., a constant or parameter); cannot reduce further *)
          Neu (nm, x, [])
      | Some (Transparent (body, _)) ->
          (* Variable is transparent (e.g., a let-bound variable); expand its definition *)
          to_whnf body env
      | None ->
          (* Variable not found in the environment; report an error *)
          create_whnf_error t env
            ("Couldn't find Variable " ^ nm ^ " " ^ Int.to_string x
           ^ " in environment"))
  | Lambda (nm, x, x_tp, body) ->
      (* Lambda abstraction is already in WHNF *)
      Lambda (nm, x, x_tp, body)
  | Product (nm, x, x_tp, body) ->
      (* Product type is already in WHNF *)
      Product (nm, x, x_tp, body)
  | TypeArrow (tp1, tp2) ->
      (* Type arrow is syntactic sugar for a product type without a parameter name *)
      Product ("", -1, tp1, tp2)
  | App (t1, t2) -> (
      (* Application of function 't1' to argument 't2' *)
      match to_whnf t1 env with
      | Neu (nm, x, ts) ->
          (* 't1' is a neutral term; build a new neutral term by adding 't2' to its arguments *)
          Neu (nm, x, t2 :: ts)
      | Neu_with_Hole (nm, tp, ts) ->
          (* 't1' is a neutral term with a hole; apply 't2' *)
          Neu_with_Hole (nm, tp, t2 :: ts)
      | Lambda (_, x, _, body) ->
          (* 't1' is a lambda abstraction; perform beta reduction by substituting 't2' for 'x' in 'body' *)
          to_whnf (substitute body (VarMap.singleton x t2)) env
      | whnf_term ->
          (* 't1' is not a function; cannot apply 't2'; report an error *)
          create_whnf_error t env
            ("When reducing Application expected Neu or Lambda\n" ^ "Got "
           ^ whnf_to_string whnf_term ^ " instead"))
  | Hole (nm, tp) ->
      (* A hole is treated as a neutral term with a hole *)
      Neu_with_Hole (nm, tp, [])
  | Let (nm, var, t1, tp_t1, t2) ->
      (* Let-binding 'let nm = t1 in t2' *)
      (* Introduce a fresh variable to avoid capture *)
      let fresh_var = fresh_var () in
      (* Add the definition of 't1' to the environment as transparent *)
      let _ = add_to_termEnv env fresh_var (Transparent (t1, tp_t1)) in
      (* Substitute 'var' with the fresh variable in 't2' and reduce *)
      let t2_whnf =
        to_whnf
          (substitute t2 (VarMap.singleton var (Ast.Var (nm, fresh_var))))
          env
      in
      (* Substitute the fresh variable with 't1' in the result *)
      let t2_whnf_substituted =
        substitute_whnf t2_whnf (VarMap.singleton fresh_var t1)
      in
      (* Remove the fresh variable from the environment *)
      let _ = rm_from_termEnv env fresh_var in
      (* Return the reduced term *)
      t2_whnf_substituted
  | Case (term, patterns) ->
      let term_whnf = to_whnf term env in
      Case (term_whnf, patterns)

(** [equiv t1 t2 env] checks if two terms [t1] and [t2] are equivalent under the
    environment [env].

    @param t1 The first term.
    @param t2 The second term.
    @param env The environment containing variable and term bindings.
    @return [true] if [t1] and [t2] are equivalent; [false] otherwise. *)
let rec equiv (t1 : Ast.term) (t2 : Ast.term) ((_, termEnv, _) as env : env) :
    bool =
  match (to_whnf t1 termEnv, to_whnf t2 termEnv) with
  | Type, Type ->
      (* Both terms are 'Type'; they are equivalent *)
      true
  | Kind, Kind ->
      (* Both terms are 'Kind'; they are equivalent *)
      true
  | IntType, IntType -> true
  | StringType, StringType -> true
  | BoolType, BoolType -> true
  | IntLit n1, IntLit n2 -> n1 = n2
  | StringLit s1, StringLit s2 -> s1 = s2
  | BoolLit b1, BoolLit b2 -> b1 = b2
  | Neu (_, x1, ts1), Neu (_, x2, ts2) ->
      (* Both terms are neutral terms *)
      (* They are equivalent if the variable identifiers are the same and their argument lists are equivalent *)
      x1 = x2
      && List.length ts1 = List.length ts2
      && List.for_all2 (fun x y -> equiv x y env) ts1 ts2
  | ( (Neu_with_Hole (_, tp1, ts1) as whnf_1),
      (Neu_with_Hole (_, tp2, ts2) as whnf_2) ) ->
      (* Both terms are neutral terms with holes *)
      if
        (* They are considered equivalent if their types are equivalent and their argument lists are equivalent *)
        equiv tp1 tp2 env
        && List.length ts1 = List.length ts2
        && List.for_all2 (fun x y -> equiv x y env) ts1 ts2
      then true
      else
        (* Types or arguments do not match; print debugging information *)
        let _ =
          print_endline
            ("Term_1 " ^ term_to_string t1 ^ "\n" ^ "Whnf_1 "
           ^ whnf_to_string whnf_1 ^ "\n" ^ "Is expected to be equal to\n"
           ^ "Term_2 " ^ term_to_string t2 ^ "\n" ^ "Whnf_2 "
           ^ whnf_to_string whnf_2 ^ "\nEnv at this moment:\n"
           ^ termEnv_to_string termEnv)
        in
        true (* Returning true here might be specific to handling holes *)
  | Lambda (nm1, x1, x1_tp, body1), Lambda (nm2, x2, x2_tp, body2)
  | Product (nm1, x1, x1_tp, body1), Product (nm2, x2, x2_tp, body2) ->
      (* Both terms are lambdas or products *)
      if equiv x1_tp x2_tp env then
        (* If the parameter types are equivalent *)
        let fresh_var = fresh_var () in
        (* Introduce a fresh variable to avoid variable capture *)
        let _ = add_to_termEnv termEnv fresh_var (Opaque x1_tp) in
        (* Substitute both bodies with the fresh variable *)
        let body1' =
          substitute body1
            (VarMap.singleton x1
               (Ast.Var (generate_fresh_var_name env nm1, fresh_var)))
        in
        let body2' =
          substitute body2
            (VarMap.singleton x2
               (Ast.Var (generate_fresh_var_name env nm2, fresh_var)))
        in
        (* Check if the bodies are equivalent *)
        let res = equiv body1' body2' env in
        (* Remove the fresh variable from the environment *)
        let _ = rm_from_termEnv termEnv fresh_var in
        res
      else
        (* Parameter types are not equivalent *)
        false
  | (Neu_with_Hole (_, _, _) as whnf_1), (_ as whnf_2)
  | (_ as whnf_1), (Neu_with_Hole (_, _, _) as whnf_2) ->
      (* One of the terms is a hole; consider them equivalent for now *)
      let _ =
        print_endline
          ("Term_1 " ^ term_to_string t1 ^ "\n" ^ "Whnf_1 "
         ^ whnf_to_string whnf_1 ^ "\n" ^ "Is expected to be equal to\n"
         ^ "Term_2 " ^ term_to_string t2 ^ "\n" ^ "Whnf_2 "
         ^ whnf_to_string whnf_2 ^ "\n Env at this moment:\n"
         ^ termEnv_to_string termEnv)
      in
      true
  | _ ->
      (* Terms are not equivalent *)
      false

(** [infer_type env term] infers the type of the given term [term] in the
    context of environment [env].

    @param env The environment containing variable and term bindings.
    @param term The term for which to infer the type.
    @return
      A pair [(t, tp)] where [t] is the term with variables resolved, and [tp]
      is the inferred type of [t].
    @raise Failure
      If type inference fails, raises an exception with an appropriate error
      message. *)
and infer_type ((_, termEnv, _) as env : env)
    ({ pos; data = t } as term : ParserAst.uTerm) : Ast.term * Ast.tp =
  match t with
  | Type ->
      (* The type of 'Type' is 'Kind' *)
      (Type, Kind)
  | Kind ->
      (* Cannot infer the type of 'Kind' *)
      create_infer_type_error pos "Can't infer the type of Kind" term env
  | IntType -> (IntType, Type)
  | StringType -> (StringType, Type)
  | BoolType -> (BoolType, Type)
  | IntLit n -> (IntLit n, IntType)
  | StringLit s -> (StringLit s, StringType)
  | BoolLit b -> (BoolLit b, BoolType)
  | Var x -> (
      (* If the term is a variable, look up its type in the environment *)
      match find_opt_in_env env x with
      | Some (y, (Opaque tp | Transparent (_, tp))) ->
          (* Variable 'x' is found with identifier 'y' and type 'tp' *)
          (Var (x, y), tp)
      | None ->
          create_infer_type_error pos ("Variable " ^ x ^ " not found") term env)
  | Lambda (_, None, _) ->
      (* Lambda expression with omitted argument type *)
      (* Cannot infer the type of a lambda without knowing the type of its argument *)
      create_infer_type_error pos
        "Can't infer the type of lambda with omitted argument type" term env
  | Lambda (x, Some tp, t) -> (
      (* Lambda with argument name 'x', argument type 'tp', and body 't' *)
      (* First, infer the type of the argument type 'tp' *)
      let tp, tp_of_tp = infer_type env tp in
      match tp_of_tp with
      | Type | Kind ->
          (* The type of the argument type 'tp' must be 'Type' or 'Kind' *)
          (* Add 'x' to the environment with type 'tp' *)
          let fresh_var = add_to_env env x (Opaque tp) in
          (* Infer the type of the body 't' *)
          let body, body_tp = infer_type env t in
          (* Remove 'x' from the environment after processing the body *)
          let _ = rm_from_env env x in
          (* The type of the lambda is a dependent function type 'Product' *)
          (Lambda (x, fresh_var, tp, body), Product (x, fresh_var, tp, body_tp))
      | _ ->
          (* The argument type 'tp' must be of type 'Type' or 'Kind' *)
          create_infer_type_error pos
            "The type of Lambda argument type must be either Type or Kind" term
            env)
  | Product (x, tp, t) -> (
      (* Product type with parameter 'x', parameter type 'tp', and body 't' *)
      (* First, infer the type of the parameter type 'tp' *)
      let tp, tp_of_tp = infer_type env tp in
      match tp_of_tp with
      | Type | Kind -> (
          (* The type of 'tp' must be 'Type' or 'Kind' *)
          (* Add 'x' to the environment with type 'tp' *)
          let fresh_var = add_to_env env x (Opaque tp) in
          (* Infer the type of the body 't' *)
          let body, body_tp = infer_type env t in
          (* Remove 'x' from the environment after processing the body *)
          let _ = rm_from_env env x in
          match body_tp with
          | Type | Kind ->
              (* The type of the body 't' must be 'Type' or 'Kind' *)
              (Product (x, fresh_var, tp, body), body_tp)
          | _ ->
              (* The body type is not 'Type' or 'Kind' *)
              create_infer_type_error pos
                "The type of Product body type must be either Type or Kind" term
                env)
      | _ ->
          (* The parameter type 'tp' must be 'Type' or 'Kind' *)
          create_infer_type_error pos
            "The type of Product argument type must be either Type or Kind" term
            env)
  | TypeArrow (tp1, tp2) -> (
      (* Function type arrow from 'tp1' to 'tp2' *)
      (* First, infer the type of the domain type 'tp1' *)
      let tp1, tp_of_tp1 = infer_type env tp1 in
      match tp_of_tp1 with
      | Type | Kind -> (
          (* The type of 'tp1' must be 'Type' or 'Kind' *)
          (* Infer the type of the codomain type 'tp2' *)
          let tp2, tp_of_tp2 = infer_type env tp2 in
          match tp_of_tp2 with
          | Type | Kind ->
              (* The type of 'tp2' must be 'Type' or 'Kind' *)
              (TypeArrow (tp1, tp2), tp_of_tp2)
          | _ ->
              (* The codomain type is not 'Type' or 'Kind' *)
              create_infer_type_error pos
                "The type of Type Arrow body type must be either Type or Kind"
                term env)
      | _ ->
          (* The domain type 'tp1' must be 'Type' or 'Kind' *)
          create_infer_type_error pos
            "The type of Type Arrow argument type must be either Type or Kind"
            term env)
  | App (t1, t2) -> (
      (* Application of function 't1' to argument 't2' *)
      (* Infer the type of 't1' *)
      let t1, t1_tp = infer_type env t1 in
      (* Reduce 't1_tp' to weak head normal form *)
      match to_whnf t1_tp termEnv with
      | Product (_, x, x_tp, tp_body) ->
          (* The type of 't1' is a function type with parameter 'x' of type 'x_tp' *)
          (* Check that 't2' has type 'x_tp' *)
          let t2 = check_type env t2 x_tp in
          (* The result type is 'tp_body' with 'x' substituted by 't2' *)
          (App (t1, t2), substitute tp_body (VarMap.singleton x t2))
      | _ ->
          (* The type of 't1' is not a function type *)
          create_infer_type_error pos
            "The type of Application's first argument must be a Product" term
            env)
  | TermWithTypeAnno (t, tp) -> (
      (* Term 't' with type annotation 'tp' *)
      (* Infer the type of the type annotation 'tp' *)
      let tp, tp_of_tp = infer_type env tp in
      match tp_of_tp with
      | Type | Kind ->
          (* The type annotation 'tp' must be of type 'Type' or 'Kind' *)
          (* Check that 't' has type 'tp' *)
          (check_type env t tp, tp)
      | _ ->
          (* The type annotation 'tp' is not of type 'Type' or 'Kind' *)
          create_infer_type_error pos "Type annotation must be a Type or Kind"
            term env)
  | Let (x, t1, t2) ->
      (* Let-binding 'let x = t1 in t2' *)
      (* Infer the type of 't1' *)
      let t1, tp_t1 = infer_type env t1 in
      (* Add 'x' to the environment with value 't1' and type 'tp_t1' *)
      let fresh_var = add_to_env env x (Transparent (t1, tp_t1)) in
      (* Infer the type of 't2' *)
      let t2, tp_t2 = infer_type env t2 in
      (* Remove 'x' from the environment *)
      let _ = rm_from_env env x in
      (* The type of the let-binding is 'tp_t2' with 'x' substituted by 't1' *)
      ( Let (x, fresh_var, t1, tp_t1, t2),
        substitute tp_t2 (VarMap.singleton fresh_var t1) )
  | LetDef (x, t1) ->
      (* Let-definition 'let x = t1' *)
      (* Infer the type of 't1' *)
      let t1, tp_t1 = infer_type env t1 in
      (* Add 'x' to the environment with value 't1' and type 'tp_t1' *)
      let _ = add_to_env env x (Transparent (t1, tp_t1)) in
      (t1, tp_t1)
  | Lemma (x, t1, t2) ->
      (* Lemma 'lemma x = t1 in t2' *)
      (* Infer the type of the proof 't1' *)
      let t1, tp_t1 = infer_type env t1 in
      (* Add 'x' to the environment as an opaque binding with type 'tp_t1' *)
      let fresh_var = add_to_env env x (Opaque tp_t1) in
      (* Infer the type of 't2' *)
      let t2, tp_t2 = infer_type env t2 in
      (* Remove 'x' from the environment *)
      let _ = rm_from_env env x in
      (* Apply the lemma by constructing 'App (Lambda (x, tp_t1, t2), t1)' *)
      ( App (Lambda (x, fresh_var, tp_t1, t2), t1),
        substitute tp_t2 (VarMap.singleton fresh_var t1) )
  | LemmaDef (x, t1) ->
      (* Lemma definition 'lemma x = t1' *)
      (* Infer the type of the proof 't1' *)
      let t1, tp_t1 = infer_type env t1 in
      (* Add 'x' to the environment as an opaque binding with type 'tp_t1' *)
      let _ = add_to_env env x (Opaque tp_t1) in
      (t1, tp_t1)
  | Hole x ->
      (* Cannot infer the type of a hole *)
      create_infer_type_error pos
        ("Trying to infer the type of a Hole " ^ x)
        term env
  | ADTSig _ | ADTDecl _ | Case _ -> infer_data_type env term

(** [check_type env term tp] checks whether the term [term] has the expected
    type [tp] in the context of environment [env].

    @param env The environment containing variable and term bindings.
    @param term The term to check.
    @param tp The expected type of the term.
    @return The term [term] with variables resolved and type-checked.
    @raise Failure
      If type checking fails, raises an exception with an appropriate error
      message. *)
and check_type ((_, termEnv, _) as env : env)
    ({ pos; data = t } as term : ParserAst.uTerm) (tp : Ast.term) : Ast.term =
  match t with
  | Type | Var _ | App _ | Product _ | TermWithTypeAnno _ | TypeArrow _
  | IntType | StringType | BoolType | IntLit _ | StringLit _ | BoolLit _ ->
      (* For these terms, infer their type and compare to the expected type *)
      let t, t_tp = infer_type env term in
      if equiv tp t_tp env then t
      else
        (* Types are not equivalent; report an error *)
        create_check_type_error pos
          ("Instead got:\n" ^ term_to_string t_tp)
          term tp env
  | Lambda (x, None, body) -> (
      (* Lambda with omitted argument type *)
      (* Reduce the expected type 'tp' to WHNF to check if it's a function type *)
      match to_whnf tp termEnv with
      | Product (_, y, y_tp, body_tp) ->
          (* The expected type is a function type with parameter 'y' of type 'y_tp' *)
          (* Add 'x' to the environment with type 'y_tp' *)
          let fresh_var = add_to_env env x (Opaque y_tp) in
          (* Check the body against the expected body type with 'y' substituted by 'x' *)
          let body' =
            check_type env body
              (substitute body_tp (VarMap.singleton y (Ast.Var (x, fresh_var))))
          in
          (* Remove 'x' from the environment *)
          let _ = rm_from_env env x in
          (* Return the lambda term with the inferred argument type *)
          Lambda (x, fresh_var, y_tp, body')
      | _ ->
          (* The expected type is not a function type *)
          create_check_type_error pos "The type of Lambda must be a Product"
            term tp env)
  | Lambda (x, Some x_tp, body) -> (
      (* Lambda with argument type annotation 'x_tp' *)
      (* First, check the lambda without the argument type against the expected type *)
      match check_type env { pos; data = Lambda (x, None, body) } tp with
      | Lambda (_, _, arg_tp, _) as lambda ->
          (* Infer the type of the provided argument type 'x_tp' *)
          let x_tp, _ = infer_type env x_tp in
          if equiv x_tp arg_tp env then
            (* The provided argument type matches the expected argument type *)
            lambda
          else
            (* Argument types do not match; report an error *)
            create_check_type_error pos
              ("Got:\n" ^ term_to_string x_tp
             ^ "\nThe expected type of lambda argument was: "
             ^ term_to_string arg_tp)
              term tp env
      | _ ->
          (* Not a lambda term; report an error *)
          create_check_type_error pos "Lambda must be lambda" term tp env)
  | Kind ->
      (* 'Kind' does not have a type; report an error *)
      create_check_type_error pos "Kind doesn't have a type" term tp env
  | Let (x, t1, t2) ->
      (* Let-binding 'let x = t1 in t2' *)
      (* Infer the type of 't1' *)
      let t1, tp_t1 = infer_type env t1 in
      (* Add 'x' to the environment with value 't1' and type 'tp_t1' *)
      let fresh_var = add_to_env env x (Transparent (t1, tp_t1)) in
      (* Check that 't2' has the expected type 'tp' *)
      let t2 = check_type env t2 tp in
      (* Remove 'x' from the environment *)
      let _ = rm_from_env env x in
      (* Return the let-binding term *)
      Let (x, fresh_var, t1, tp_t1, t2)
  | Lemma (x, t1, t2) ->
      (* Lemma 'lemma x = t1 in t2' *)
      (* Infer the type of the proof 't1' *)
      let t1, tp_t1 = infer_type env t1 in
      (* Add 'x' to the environment as an opaque binding with type 'tp_t1' *)
      let fresh_var = add_to_env env x (Opaque tp_t1) in
      (* Check that 't2' has the expected type 'tp' *)
      let t2 = check_type env t2 tp in
      (* Remove 'x' from the environment *)
      let _ = rm_from_env env x in
      (* Apply the lemma by constructing 'App (Lambda (x, tp_t1, t2), t1)' *)
      App (Lambda (x, fresh_var, tp_t1, t2), t1)
  | Hole nm ->
      (* Record that the hole 'nm' has been assigned type 'tp' *)
      let _ =
        print_endline
          ("Hole " ^ nm ^ " was assigned type " ^ term_to_string tp
         ^ "\nThe state of the environment at that moment:\n"
         ^ env_to_string env)
      in
      (* Return the hole with its type *)
      Hole (nm, tp)
  | LemmaDef (_, t) | LetDef (_, t) ->
      (* For lemma or let definitions, check that 't' has the expected type 'tp' *)
      check_type env t tp
  | ADTSig _ | ADTDecl _ | Case _ -> check_data_type env term tp

and infer_data_type ((_, termEnv, adtEnv) as env : env)
    ({ pos; data = t } as term : ParserAst.uTerm) : Ast.term * Ast.term =
  match t with
  | ADTSig (nm, ts) ->
      let ts' = telescope_check_type_and_extend_env env ts in
      let _ = add_to_adtEnv adtEnv nm (AdtTSig (ts', [])) in
      let adt_sig_tp = build_adt_sig env ts' in
      let fresh_var = add_to_env env nm (Opaque adt_sig_tp) in
      let _ = rm_telescope_from_env env ts' in
      (Var (nm, fresh_var), adt_sig_tp)
  | ADTDecl (nm, ts, cs) ->
      let ts' = telescope_check_type_and_extend_env env ts in
      let dataCNames =
        List.map (fun { ParserAst.cname = nmCon; _ } -> nmCon) cs
      in
      let _ = add_to_adtEnv adtEnv nm (AdtTSig (ts', dataCNames)) in
      let adt_sig_tp = build_adt_sig env ts' in
      let fresh_var = add_to_env env nm (Opaque adt_sig_tp) in
      let con_list =
        List.map
          (fun { ParserAst.cname = nmCon; ParserAst.telescope = tsCon } ->
            let tsCon' = telescope_check_type_and_extend_env env tsCon in
            let _ = add_to_adtEnv adtEnv nmCon (AdtDSig (nm, tsCon')) in
            let _ = rm_telescope_from_env env tsCon' in
            { Ast.cname = nmCon; Ast.telescope = tsCon' })
          cs
      in
      let _ = rm_telescope_from_env env ts' in
      let cs =
        List.map
          (fun (data_con : Ast.constructorDef) ->
            build_adt_data env ts' data_con.telescope [] (nm, fresh_var))
          con_list
      in
      let _ =
        List.map
          (fun (nmCon, tpCon) -> add_to_env env nmCon (Opaque tpCon))
          (List.combine
             (List.map
                (fun (data_con : Ast.constructorDef) -> data_con.cname)
                con_list)
             cs)
      in
      (Var (nm, fresh_var), adt_sig_tp)
  | Case (scrut, ps) -> (
      let scrut', tp' = infer_type env scrut in
      match to_whnf tp' termEnv with
      | Neu (nm, _, tsT_args) -> (
          let tsT_args = List.rev tsT_args in
          match find_opt_in_adtEnv adtEnv nm with
          | Some (AdtTSig (tsT, dataCNames)) ->
              if telescope_length tsT = List.length tsT_args then
                let patterns, result_type =
                  check_pattern_matching_branches env ps tsT tsT_args dataCNames
                in
                (Case (scrut', patterns), result_type)
              else
                create_infer_type_error pos
                  "The number of Scrutinee's type arguments must match the ADT \
                   signature"
                  term env
          | Some (AdtDSig _) ->
              create_infer_type_error pos
                "Scrutinee's type should be an ADT type and not an ADT \
                 constructor"
                term env
          | None ->
              create_infer_type_error pos
                "Scrutinee's type should be an ADT type" term env)
      | _ ->
          create_infer_type_error pos
            "Scrutinee's type whnf form should be a neutral term" term env)
  | Type | Kind | Var _ | App _ | Product _ | TermWithTypeAnno _ | TypeArrow _
  | IntType | StringType | BoolType | IntLit _ | StringLit _ | BoolLit _
  | Lambda _ | Let _ | LetDef _ | Lemma _ | LemmaDef _ | Hole _ ->
      create_infer_type_error pos "Expected ADT declaration" term env

and check_data_type ((_, _, _) as env : env)
    ({ pos; data = t } as term : ParserAst.uTerm) (tp : Ast.term) : Ast.term =
  match t with
  | ADTDecl _ | ADTSig _ | Case _ ->
      let t', tp' = infer_data_type env term in
      if equiv tp tp' env then t'
      else
        create_check_type_error pos
          ("Instead got:\n" ^ term_to_string tp')
          term tp env
  | Type | Kind | Var _ | App _ | Product _ | TermWithTypeAnno _ | TypeArrow _
  | IntType | StringType | BoolType | IntLit _ | StringLit _ | BoolLit _
  | Lambda _ | Let _ | LetDef _ | Lemma _ | LemmaDef _ | Hole _ ->
      create_infer_type_error pos "Expected ADT declaration" term env

and telescope_check_type_and_extend_env (env : env)
    (telescope : ParserAst.telescope) : Ast.telescope =
  match telescope with
  | Empty -> Empty
  | Cons (nm, tp, ts) ->
      let tp', _ = infer_type env tp in
      let fresh_var = add_to_env env nm (Opaque tp') in
      let res =
        Ast.Cons (nm, fresh_var, tp', telescope_check_type_and_extend_env env ts)
      in
      res

and build_adt_sig (env : env) (ts : Ast.telescope) : Ast.term =
  match ts with
  | Empty -> Type
  | Cons (nm, var, tp, ts) ->
      let res : Ast.term = Product (nm, var, tp, build_adt_sig env ts) in
      res

and build_adt_data (env : env) (tsType : Ast.telescope) (tsData : Ast.telescope)
    (var_list : (string * Ast.var) list) (adt_sig_var : string * Ast.var) :
    Ast.term =
  match tsType with
  | Empty -> (
      match tsData with
      | Empty ->
          let adt_nm, adt_var = adt_sig_var in
          List.fold_left
            (fun acc (nm, var) -> Ast.App (acc, Var (nm, var)))
            (Ast.Var (adt_nm, adt_var))
            (List.rev var_list)
      | Cons (nm, var, tp, ts) ->
          let res : Ast.term =
            Product
              (nm, var, tp, build_adt_data env tsType ts var_list adt_sig_var)
          in
          res)
  | Cons (nm, var, tp, ts) ->
      let res : Ast.term =
        Product
          ( nm,
            var,
            tp,
            build_adt_data env ts tsData ((nm, var) :: var_list) adt_sig_var )
      in
      res

and check_pattern_matching_branches (env : env) (ps : ParserAst.matchPat list)
    (tsT : Ast.telescope) (tsT_types : Ast.tp list)
    (dataCNames : Ast.dataCName list) : Ast.matchPat list * Ast.tp =
  let infer_branch_and_extend_env ((uTermEnv, _, _) as env : env)
      (tsT : Ast.telescope) (tsT_types : Ast.tp list) (tsD : Ast.telescope)
      (args : string list) ({ pos; _ } as term : ParserAst.uTerm) :
      Ast.term * Ast.tp * (string * Ast.var) list =
    let rec add_tsT_to_env (env : env) (tsT : Ast.telescope)
        (tsT_types : Ast.tp list) (argsT : string list) :
        (Ast.var * (string * Ast.var)) list =
      match tsT with
      | Empty -> []
      | Cons (_, var, tp, tsT) ->
          let concrete_tp = List.hd tsT_types in
          let new_nm = List.hd argsT in
          let fresh_var =
            add_to_env env new_nm (Transparent (concrete_tp, tp))
          in
          let tsT =
            substitute_in_telescope tsT
              (VarMap.singleton var (Ast.Var (new_nm, fresh_var)))
          in
          (var, (new_nm, fresh_var))
          :: add_tsT_to_env env tsT (List.tl tsT_types) (List.tl argsT)
    in

    let rec add_tsD_to_env (env : env) (tsD : Ast.telescope)
        (argsD : string list) : (Ast.var * (string * Ast.var)) list =
      match tsD with
      | Empty -> []
      | Cons (_, var, tp, tsD) ->
          let new_nm = List.hd argsD in
          let fresh_var = add_to_env env new_nm (Opaque tp) in
          let tsD =
            substitute_in_telescope tsD
              (VarMap.singleton var (Ast.Var (new_nm, fresh_var)))
          in
          (var, (new_nm, fresh_var)) :: add_tsD_to_env env tsD (List.tl argsD)
    in

    if telescope_length tsT + telescope_length tsD = List.length args then
      let argsT, argsD = split_pattern_args (telescope_length tsT) args in
      let tsT_all_vars = add_tsT_to_env env tsT tsT_types argsT in
      let tsD =
        substitute_in_telescope tsD
          (VarMap.of_list
             (List.map
                (fun (var, (new_nm, new_var)) ->
                  (var, Ast.Var (new_nm, new_var)))
                tsT_all_vars))
      in
      let tsD_all_vars = add_tsD_to_env env tsD argsD in
      let ts_all_vars = tsT_all_vars @ tsD_all_vars in
      let term, tp' = infer_type env term in
      let ts_names, ts_vars = List.split (snd (List.split ts_all_vars)) in
      (* We need to remove the names from the env as the branches could over shadow each others variables but
       we need to keep the internal representation in order to check if all branches have matching types *)
      let _ = List.iter (fun nm -> Env.rm_from_uTermEnv uTermEnv nm) ts_names in
      (term, tp', List.combine ts_names ts_vars)
    else
      create_infer_type_error pos
        "The number of arguments in branch's pattern must match the telescope"
        term env
  in
  let infer_and_check_all_branches ((_, termEnv, _) as env : env)
      (ps : ParserAst.matchPat list) (tsT : Ast.telescope)
      (tsT_types : Ast.tp list) (dataCNames : Ast.dataCName list) :
      (Ast.matchPat * Ast.tp) list =
    let rec loop_over_branches ((_, _, adtEnv) as env : env)
        (ps : ParserAst.matchPat list) (tsT : Ast.telescope)
        (tsT_types : Ast.tp list) (dataCNames : Ast.dataCName list) :
        ((Ast.matchPat * Ast.tp) * (string * Ast.var) list) list =
      match ps with
      | (pattern, uTerm) :: (_ :: _ as ps) -> (
          match pattern with
          | PatCon (dataCName, args) ->
              if List.mem dataCName dataCNames then
                match find_opt_in_adtEnv adtEnv dataCName with
                | Some (AdtDSig (_, tsD)) ->
                    let term, tp', ts_names_and_vars =
                      infer_branch_and_extend_env env tsT tsT_types tsD args
                        uTerm
                    in
                    let dataCNames =
                      List.filter (fun x -> not (x = dataCName)) dataCNames
                    in
                    ( ((Ast.PatCon (dataCName, ts_names_and_vars), term), tp'),
                      ts_names_and_vars )
                    :: loop_over_branches env ps tsT tsT_types dataCNames
                | Some (AdtTSig _) ->
                    failwith
                      "Branch's pattern must be an ADT contructor. Found ADT \
                       type signature instead"
                | None -> failwith "Branch's pattern must be an ADT constructor"
              else
                failwith
                  "Pattern's constructor name not found in constructor list"
          | PatWild -> failwith "Wildcard pattern must be at the end")
      | (pattern, uTerm) :: [] -> (
          match pattern with
          | PatCon (dataCName, args) ->
              if List.mem dataCName dataCNames then
                match find_opt_in_adtEnv adtEnv dataCName with
                | Some (AdtDSig (_, tsD)) ->
                    let term, tp', ts_names_and_vars =
                      infer_branch_and_extend_env env tsT tsT_types tsD args
                        uTerm
                    in
                    let dataCNames =
                      List.filter (fun x -> not (x = dataCName)) dataCNames
                    in
                    if List.is_empty dataCNames then
                      ( ((Ast.PatCon (dataCName, ts_names_and_vars), term), tp'),
                        ts_names_and_vars )
                      :: []
                    else
                      failwith
                        "Expected list of constructor names to be empty, \
                         looped over all branches"
                | Some (AdtTSig _) ->
                    failwith
                      "Branch's pattern must be an ADT contructor. Found ADT \
                       type signature instead"
                | None -> failwith "Branch's pattern must be an ADT constructor"
              else
                failwith
                  "Pattern's constructor name not found in constructor list"
          | PatWild ->
              let term, tp', ts_names_and_vars =
                infer_branch_and_extend_env env Empty [] Empty [] uTerm
              in
              if List.is_empty ts_names_and_vars then
                (((Ast.PatWild, term), tp'), ts_names_and_vars) :: []
              else
                failwith
                  "Type inferences of branch with wildcard pattern shouldn't \
                   extend the environment")
      | [] -> failwith "There are no branches to check"
    in
    let check_branch_types (env : env) (branch_types : Ast.tp list) : unit =
      let hd = List.hd branch_types in
      let _, isSameType =
        List.fold_left
          (fun (prev_tp, cond) tp -> (tp, cond && equiv prev_tp tp env))
          (hd, true) (List.tl branch_types)
      in
      if isSameType then ()
      else failwith "Pattern matching branches have different types"
    in

    let result, tp_names_and_vars =
      List.split (loop_over_branches env ps tsT tsT_types dataCNames)
    in
    let _ = check_branch_types env (snd (List.split result)) in
    let all_ts_vars = snd (List.split (List.flatten tp_names_and_vars)) in
    let _ =
      List.iter (fun var -> Env.rm_from_termEnv termEnv var) all_ts_vars
    in
    result
  in
  let check_constructor_names (ps : ParserAst.matchPat list)
      (dataCNames : Ast.dataCName list) : bool =
    let rec collect_constructor_names (ps : ParserAst.matchPat list) :
        string list * bool =
      match ps with
      | (PatCon (dataCName, _), _) :: ps ->
          let cs, contaisWild = collect_constructor_names ps in
          (dataCName :: cs, contaisWild)
      | (PatWild, _) :: ps ->
          let cs, contaisWild = collect_constructor_names ps in
          if contaisWild then
            failwith "There can't be more than 1 wildcard branch"
          else (cs, true)
      | [] -> ([], false)
    in
    let cs, containsWild = collect_constructor_names ps in
    if
      containsWild
      && List.compare_lengths cs dataCNames < 0
      && List.fold_left (fun acc x -> acc && List.mem x dataCNames) true cs
    then true
    else if
      (not containsWild)
      && List.compare_lengths cs dataCNames == 0
      && List.fold_left (fun acc x -> acc && List.mem x dataCNames) true cs
    then true
    else false
  in

  if check_constructor_names ps dataCNames then
    let branches, tps =
      List.split (infer_and_check_all_branches env ps tsT tsT_types dataCNames)
    in
    if List.is_empty tps then
      failwith "List of inferred types of branches is empty"
    else (branches, List.hd tps)
  else failwith "Branches' pattern constructors mismatch"

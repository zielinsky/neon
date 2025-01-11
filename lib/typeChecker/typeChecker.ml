open Ast
open PrettyPrinter
open Env

module VarMap = Map.Make (Int)

type sub_map = term VarMap.t

(** [create_infer_type_error pos error_msg term env] raises a failure exception with an error message when an error occurs during type inference of [term]. It prints detailed information about the term, the error, and the environment.

    @param pos The position in the source code where the error occurred.
    @param error_msg A message describing the error.
    @param term The term whose type was being inferred when the error occurred.
    @param env The environment at the time of the error.
    @raise Failure Always raises a [Failure] exception with an error message including the line and column number.
*)
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

(** [create_check_type_error pos error_msg term tp env] raises a failure exception with an error message when an error occurs during type checking of [term] against the expected type [tp]. It prints detailed information about the term, the expected type, the error, and the environment.

    @param pos The position in the source code where the error occurred.
    @param error_msg A message describing the error.
    @param term The term that was being type-checked when the error occurred.
    @param tp The expected type of the term.
    @param env The environment at the time of the error.
    @raise Failure Always raises a [Failure] exception with an error message including the line and column number.
*)
let create_check_type_error (pos : ParserAst.position) (error_msg : string)
    (term : ParserAst.uTerm) (tp : tp) (env : env) : 'a =
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

(** [create_whnf_error term env error_msg] raises a failure exception with an error message when an error occurs during the conversion of [term] to its weak head normal form (WHNF). It prints detailed information about the term, the error, and the environment.

    @param term The term that was being converted to WHNF when the error occurred.
    @param env The term environment at the time of the error.
    @param error_msg A message describing the error.
    @raise Failure Always raises a [Failure] exception with an error message.
*)
let create_whnf_error (term : term) (env : termEnv) (error_msg : string) : 'a =
  let _ =
    print_endline
      ("While converting term " ^ term_to_string term ^ "\nto WHNF"
     ^ "\n\nThe following error occurred:\n\t" ^ error_msg ^ "\n"
     ^ "\nThe state of the environment at that moment:\n"
     ^ termEnv_to_string env)
  in
  failwith "Error when converting to WHNF"

(** [substitute t sub] performs capture-avoiding substitution on term [t] using the substitution map [sub]. It replaces variables in [t] according to [sub], ensuring that bound variables are correctly handled to prevent variable capture.

    @param t The term in which to perform substitution.
    @param sub The substitution map, mapping variable identifiers to terms.
    @return A new term where variables have been substituted according to [sub].
*)
let rec substitute (t : term) (sub : sub_map) : term =
  match t with
  | Var (nm, x) -> (
      match VarMap.find_opt x sub with Some t -> t | None -> Var (nm, x))
  | Lambda (nm, x, tp, body) ->
      let y = fresh_var () in
      Lambda
        ( nm,
          y,
          substitute tp sub,
          substitute body (VarMap.add x (Var (nm, y)) sub) )
  | Product (nm, x, tp, body) ->
      let y = fresh_var () in
      Product
        ( nm,
          y,
          substitute tp sub,
          substitute body (VarMap.add x (Var (nm, y)) sub) )
  | App (t1, t2) -> App (substitute t1 sub, substitute t2 sub)
  | TypeArrow (t1, t2) -> TypeArrow (substitute t1 sub, substitute t2 sub)
  | Let (nm, x, t, tp_t, body) ->
      let y = fresh_var () in
      Let
        ( nm,
          y,
          substitute t sub,
          substitute tp_t sub,
          substitute body (VarMap.add x (Var (nm, y)) sub) )
  | Type | Kind | Hole _ | IntType | StringType | BoolType | IntLit _ | StringLit _ | BoolLit _ -> t

(** [substitute_whnf t sub] performs substitution on a term in weak head normal form (WHNF) [t] using the substitution map [sub].

    @param t The WHNF term in which to perform substitution.
    @param sub The substitution map.
    @return A new WHNF term with substitutions applied.
*)
let substitute_whnf (t : whnf) (sub : sub_map) : whnf =
  match t with
  | Type | Kind | IntType  | StringType | BoolType | IntLit _  | StringLit _ | BoolLit _ -> t
  | Neu (nm, var, term_list) ->
      Neu (nm, var, List.map (fun t -> substitute t sub) term_list)
  | Neu_with_Hole (nm, tp, term_list) ->
      Neu_with_Hole (nm, tp, List.map (fun t -> substitute t sub) term_list)
  | Lambda (nm, var, tp, body) ->
      Lambda (nm, var, substitute tp sub, substitute body sub)
  | Product (nm, var, tp, body) ->
      Product (nm, var, substitute tp sub, substitute body sub)

(** [to_whnf t env] converts a term [t] to its weak head normal form (WHNF) in the context of environment [env].

    @param t The term to convert to WHNF.
    @param env The term environment.
    @return The WHNF form of [t].
    @raise Failure If an error occurs during conversion, raises a failure with an appropriate error message.
*)
let rec to_whnf (t : term) (env : termEnv) : whnf =
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
          create_whnf_error t env ("Variable " ^ nm ^ " " ^ Int.to_string x))
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
        to_whnf (substitute t2 (VarMap.singleton var (Var (nm, fresh_var)))) env
      in
      (* Substitute the fresh variable with 't1' in the result *)
      let t2_whnf_substituted =
        substitute_whnf t2_whnf (VarMap.singleton fresh_var t1)
      in
      (* Remove the fresh variable from the environment *)
      let _ = rm_from_termEnv env fresh_var in
      (* Return the reduced term *)
      t2_whnf_substituted

(** [equiv t1 t2 env] checks if two terms [t1] and [t2] are equivalent under the environment [env].

    @param t1 The first term.
    @param t2 The second term.
    @param env The environment containing variable and term bindings.
    @return [true] if [t1] and [t2] are equivalent; [false] otherwise.
*)
let rec equiv (t1 : term) (t2 : term) ((_, termEnv, _) as env : env) : bool =
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
            (VarMap.singleton x1 (Var (generate_fresh_var_name env nm1, fresh_var)))
        in
        let body2' =
          substitute body2
            (VarMap.singleton x2 (Var (generate_fresh_var_name env nm2, fresh_var)))
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


(** [infer_type env term] infers the type of the given term [term] in the context of environment [env].

    @param env The environment containing variable and term bindings.
    @param term The term for which to infer the type.
    @return A pair [(t, tp)] where [t] is the term with variables resolved, and [tp] is the inferred type of [t].
    @raise Failure If type inference fails, raises an exception with an appropriate error message.
*)
and infer_type ((_, termEnv, _) as env : env)
    ({ pos; data = t } as term : ParserAst.uTerm) : term * term =
  match t with
  | Type ->
      (* The type of 'Type' is 'Kind' *)
      (Type, Kind)
  | Kind ->
      (* Cannot infer the type of 'Kind' *)
      create_infer_type_error pos "Can't infer the type of Kind" term env
	| IntType ->
		(IntType, Type)
	| StringType ->
        (StringType, Type)
	| BoolType ->
        (BoolType, Type)
	| IntLit n ->
        (IntLit n, IntType)
	| StringLit s ->
        (StringLit s, StringType)
	| BoolLit b ->
        (BoolLit b, BoolType)
  | Var x -> 
      (* If the term is a variable, look up its type in the environment *)
      begin match find_opt_in_env env x with
      | Some (y, (Opaque tp | Transparent (_, tp))) ->
          (* Variable 'x' is found with identifier 'y' and type 'tp' *)
          (Var (x, y), tp)
      | None -> create_infer_type_error pos ("Variable " ^ x ^ " not found") term env
        (* begin match find_opt_in_adtEnv adtEnv x with
        | Some (AdtTSig ts) -> ((Var x ), build_adt_sig env ts)
        | Some (AdtDSig (nm, ts)) -> failwith "TODO"
        | None -> create_infer_type_error pos ("Variable " ^ x ^ " not found") term env
        end *)
      end
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
  | ADTSig _ | ADTDecl _ ->
    infer_data_type env term


(** [check_type env term tp] checks whether the term [term] has the expected type [tp] in the context of environment [env].

    @param env The environment containing variable and term bindings.
    @param term The term to check.
    @param tp The expected type of the term.
    @return The term [term] with variables resolved and type-checked.
    @raise Failure If type checking fails, raises an exception with an appropriate error message.
*)
and check_type ((_, termEnv, _) as env : env)
    ({ pos; data = t } as term : ParserAst.uTerm) (tp : term) : term =
  match t with
  | Type | Var _ | App _ | Product _  | TermWithTypeAnno _ | TypeArrow _ | IntType | StringType | BoolType | IntLit _ | StringLit _ | BoolLit _ ->
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
              (substitute body_tp (VarMap.singleton y (Var (x, fresh_var))))
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
  | ADTSig _ | ADTDecl _ ->
    check_data_type env term tp
and infer_data_type ((_, _, adtEnv) as env : env)
({ pos; data = t } as term : ParserAst.uTerm) : term * term =
    match t with
    | ADTSig (nm, ts) -> 
        let ts' = telescope_check_type env ts in
        let _ = add_to_adtEnv adtEnv nm (AdtTSig ts') in
        let adt_sig_tp = build_adt_sig env ts' in
        let fresh_var = add_to_env env nm (Opaque adt_sig_tp) in
        ((Var (nm, fresh_var)), adt_sig_tp)
    | ADTDecl (nm, ts, cs) -> 
        let ts' = telescope_check_type env ts in
        let _ = add_to_adtEnv adtEnv nm (AdtTSig ts') in
        let adt_sig_tp = build_adt_sig env ts' in
        let fresh_var = add_to_env env nm (Opaque adt_sig_tp) in
        let _ = add_telescope_to_env env ts' in
        let con_list = List.map (fun { ParserAst.cname = nmCon; ParserAst.telescope = tsCon } -> (
            let tsCon' = telescope_check_type env tsCon in
            let _ = add_to_adtEnv adtEnv nmCon (AdtDSig(nm, tsCon')) in
            { cname = nmCon; telescope = tsCon' }
        )) cs in
        let _ = rm_telescope_from_env env ts' in
        let cs = List.map (fun data_con -> build_adt_data env ts' data_con.telescope ((nm, fresh_var) :: [])) con_list in
        let _ = List.map (fun (nmCon, tpCon) -> add_to_env env nmCon (Opaque tpCon)) (List.combine (List.map (fun data_con -> data_con.cname) con_list) cs) in

        ((Var (nm, fresh_var)), adt_sig_tp) (* TODO *)
    | Type | Kind | Var _ | App _ | Product _ | TermWithTypeAnno _ | TypeArrow _ | IntType | StringType | BoolType | IntLit _ | StringLit _ | BoolLit _ | Lambda _ | Let _ | LetDef _ | Lemma _ | LemmaDef _ | Hole _ -> 
        create_infer_type_error pos "Expected ADT declaration" term env

and check_data_type ((_, _, _) as env : env)
  ({ pos; data = t } as term : ParserAst.uTerm) (tp : term) : term =
      match t with
      | ADTDecl _ | ADTSig _  -> 
          let t', tp' = infer_data_type env term in
          if equiv tp tp' env then t'
          else
            create_check_type_error pos
              ("Instead got:\n" ^ term_to_string tp')
              term tp env
      | Type | Kind | Var _ | App _ | Product _ | TermWithTypeAnno _ | TypeArrow _ | IntType | StringType | BoolType | IntLit _ | StringLit _ | BoolLit _ | Lambda _ | Let _ | LetDef _ | Lemma _ | LemmaDef _ | Hole _ -> 
          create_infer_type_error pos "Expected ADT declaration" term env

(* Potentially use subst function on the telescope as we map through it*)
and telescope_check_type (env : env) (telescope : ParserAst.telescope) : Ast.telescope =
  match telescope with
  | Empty -> Empty
  | Cons (nm, tp, ts) -> 
      let tp', _ = infer_type env tp in
      let _ = add_to_env env nm (Opaque tp') in
      let res = Cons (nm, tp', telescope_check_type env ts) in
      let _ = rm_from_env env nm in
      res
and build_adt_sig (env: env) (ts: telescope) : term = 
match ts with
| Empty -> Type
| Cons (nm, tp, ts) -> 
  let fresh_var = add_to_env env nm (Opaque tp) in
  Product (nm, fresh_var, tp, (build_adt_sig env ts))
and build_adt_data (env: env) (tsType: telescope) (tsData: telescope) (var_list: (string * var) list) : term =
  match tsType with
  | Empty -> 
    begin match tsData with
    | Empty -> 
      let (nm, var) = (List.hd var_list) in
      List.fold_left (fun acc (nm, var) -> App(Var (nm, var), acc)) (Var(nm, var)) (List.tl var_list)
    | Cons (nm, tp ,ts) -> 
      let fresh_var = add_to_env env nm (Opaque tp) in
      let res = TypeArrow (Var(nm, fresh_var), build_adt_data env tsType ts var_list) in
      let _ = rm_from_env env nm in
      res 
    end
  | Cons (nm, tp, ts) ->
    let fresh_var = add_to_env env nm (Opaque tp) in
    let res: term = Product (nm, fresh_var, tp, (build_adt_data env ts tsData ((nm, fresh_var) :: var_list))) in
    let _ = rm_from_env env nm in
    res 

  (* 
  data Maybe A = 
  | Just : forall A. A -> Maybe A
  forall A. A -> Maybe A

  ADT Sig Type (Maybe) = Pi (A: Type) => Type
  ADT Con Type (Just) = Pi (A: Type) => (x: A) -> App(Maybe, A)
  ADT Con Type (Just) = Pi (A: Type) => (x: A) -> Type
  Maybe A
  Maybe -> forall A. 


  data Maybe A = ...


  (Just Int 5) -> 

  Maybe A B = App(App(Maybe, A), B)
  fun foo ... = Just Int 5
  *)
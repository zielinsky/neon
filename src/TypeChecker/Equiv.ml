let unpack (x : bool option) : bool = match x with Some b -> b | None -> false

(** [equiv_optional t1 t2 env] checks if two terms [t1] and [t2] are equivalent
    under the environment [env].

    @param t1 The first term.
    @param t2 The second term.
    @param env The environment containing variable and term bindings.
    @return [true] if [t1] and [t2] are equivalent; [false] otherwise. *)
let rec equiv_optional (t1 : Core.term) (t2 : Core.term) (env : Env.termEnv) :
    bool option =
  match (Whnf.to_whnf t1 env, Whnf.to_whnf t2 env) with
  | Type, Type ->
      (* Both terms are 'Type'; they are equivalent *)
      Some true
  | Kind, Kind ->
      (* Both terms are 'Kind'; they are equivalent *)
      Some true
  | IntType, IntType -> Some true
  | StringType, StringType -> Some true
  | BoolType, BoolType -> Some true
  | IntLit n1, IntLit n2 -> Some (n1 = n2)
  | StringLit s1, StringLit s2 -> Some (s1 = s2)
  | BoolLit b1, BoolLit b2 -> Some (b1 = b2)
  | Neu (_, x1, ts1), Neu (_, x2, ts2) ->
      (* Both terms are neutral terms *)
      (* They are equivalent if the variable identifiers are the same and their argument lists are equivalent *)
      Some
        (x1 = x2
        && List.length ts1 = List.length ts2
        && List.for_all2 (fun x y -> equiv x y env) ts1 ts2)
  | ( (Neu_with_Hole (_, tp1, ts1) as whnf_1),
      (Neu_with_Hole (_, tp2, ts2) as whnf_2) ) ->
      (* Both terms are neutral terms with holes *)
      if
        (* They are considered equivalent if their types are equivalent and their argument lists are equivalent *)
        equiv tp1 tp2 env
        && List.length ts1 = List.length ts2
        && List.for_all2 (fun x y -> equiv x y env) ts1 ts2
      then Some true
      else
        (* Types or arguments do not match; print debugging information *)
        let _ =
          print_endline
            ("Term_1 "
            ^ PrettyPrinter.term_to_string t1
            ^ "\n" ^ "Whnf_1 "
            ^ PrettyPrinter.whnf_to_string whnf_1
            ^ "\n" ^ "Is expected to be equal to\n" ^ "Term_2 "
            ^ PrettyPrinter.term_to_string t2
            ^ "\n" ^ "Whnf_2 "
            ^ PrettyPrinter.whnf_to_string whnf_2
            ^ "\nEnv at this moment:\n" ^ Env.termEnv_to_string env)
        in
        Some true (* Returning Some here might be specific to handling holes *)
  | Lambda (nm1, x1, x1_tp, body1), Lambda (nm2, x2, x2_tp, body2)
  | Product (nm1, x1, x1_tp, body1), Product (nm2, x2, x2_tp, body2) ->
      (* Both terms are lambdas or products *)
      if equiv x1_tp x2_tp env then
        (* If the parameter types are equivalent *)
        let fresh_var = Env.fresh_var () in
        (* Introduce a fresh variable to avoid variable capture *)
        let _ = Env.add_to_termEnv env fresh_var (Opaque x1_tp) in
        (* Substitute both bodies with the fresh variable *)
        let body1' =
          Substitution.substitute body1
            (Substitution.singleton_sub_map x1
               (Core.Var (Env.generate_fresh_var_name nm1, fresh_var)))
        in
        let body2' =
          Substitution.substitute body2
            (Substitution.singleton_sub_map x2
               (Core.Var (Env.generate_fresh_var_name nm2, fresh_var)))
        in
        (* Check if the bodies are equivalent *)
        let res = equiv_optional body1' body2' env in
        (* Remove the fresh variable from the environment *)
        let _ = Env.rm_from_termEnv env fresh_var in
        res
      else
        (* Parameter types are not equivalent *)
        Some false
  | (Neu_with_Hole (_, _, _) as whnf_1), (_ as whnf_2)
  | (_ as whnf_1), (Neu_with_Hole (_, _, _) as whnf_2) ->
      (* One of the terms is a hole; consider them equivalent for now *)
      let _ =
        print_endline
          ("Term_1 "
          ^ PrettyPrinter.term_to_string t1
          ^ "\n" ^ "Whnf_1 "
          ^ PrettyPrinter.whnf_to_string whnf_1
          ^ "\n" ^ "Is expected to be equal to\n" ^ "Term_2 "
          ^ PrettyPrinter.term_to_string t2
          ^ "\n" ^ "Whnf_2 "
          ^ PrettyPrinter.whnf_to_string whnf_2
          ^ "\n Env at this moment:\n" ^ Env.termEnv_to_string env)
      in
      Some true
  | _ ->
      (* Terms are not equivalent *)
      None

and equiv (t1 : Core.term) (t2 : Core.term) (env : Env.termEnv) : bool =
  unpack (equiv_optional t1 t2 env)

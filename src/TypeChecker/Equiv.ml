(** [equiv t1 t2 env] checks if two terms [t1] and [t2] are equivalent under the
    environment [env].

    @param t1 The first term.
    @param t2 The second term.
    @param env The environment containing variable and term bindings.
    @return [true] if [t1] and [t2] are equivalent; [false] otherwise. *)
let rec equiv (t1 : Core.term) (t2 : Core.term) (env : Env.internal) : bool =
  match (Whnf.to_whnf t1 env, Whnf.to_whnf t2 env) with
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
            ("Term_1 "
            ^ PrettyPrinter.term_to_string t1
            ^ "\n" ^ "Whnf_1 "
            ^ PrettyPrinter.whnf_to_string whnf_1
            ^ "\n" ^ "Is expected to be equal to\n" ^ "Term_2 "
            ^ PrettyPrinter.term_to_string t2
            ^ "\n" ^ "Whnf_2 "
            ^ PrettyPrinter.whnf_to_string whnf_2
            ^ "\nEnv at this moment:\n"
            ^ Env.internal_env_to_string env)
        in
        true (* Returning Some here might be specific to handling holes *)
  | Lambda (nm1, x1, x1_tp, body1), Lambda (nm2, x2, x2_tp, body2)
  | Product (nm1, x1, x1_tp, body1), Product (nm2, x2, x2_tp, body2) ->
      (* Both terms are lambdas or products *)
      if equiv x1_tp x2_tp env then
        (* If the parameter types are equivalent *)
        let fresh_var = Env.fresh_var () in
        (* Introduce a fresh variable to avoid variable capture *)
        let _ = Env.add_to_internal_env env fresh_var (Opaque x1_tp) in
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
        let res = equiv body1' body2' env in
        (* Remove the fresh variable from the environment *)
        let _ = Env.rm_from_internal_env env fresh_var in
        res
      else
        (* Parameter types are not equivalent *)
        false
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
          ^ "\n Env at this moment:\n"
          ^ Env.internal_env_to_string env)
      in
      true
  | Refl (t1, t1_tp), Refl (t2, t2_tp) ->
      equiv t1 t2 env && equiv t1_tp t2_tp env
  | EqType (t1, t2, tp1), EqType (t3, t4, tp2) ->
      equiv t1 t3 env && equiv t2 t4 env && equiv tp1 tp2 env
  | ( Case (_, scrut1_tp, maybe_var1, res_type1, branches1),
      Case (_, scrut2_tp, maybe_var2, res_type2, branches2) ) ->
      let _ =
        match maybe_var1 with
        | Some (_, var1) -> Env.add_to_internal_env env var1 (Opaque scrut1_tp)
        | None -> ()
      in
      let _ =
        match maybe_var2 with
        | Some (_, var2) -> Env.add_to_internal_env env var2 (Opaque scrut2_tp)
        | None -> ()
      in
      let eq_res_types = equiv res_type1 res_type2 env in
      let eq_scrut_types = equiv scrut1_tp scrut2_tp env in

      let eq_branches =
        List.length branches1 = List.length branches2
        && List.fold_left
             (fun acc (b1, b2) ->
               acc
               &&
               match (b1, b2) with
               | (Core.PatCon (nm1, args1), t1), (Core.PatCon (nm2, args2), t2)
                 ->
                   if nm1 = nm2 then
                     let _ =
                       List.iter
                         (fun (_, var, tp) ->
                           Env.add_to_internal_env env var (Env.Opaque tp))
                         args1
                     in
                     let _ =
                       List.iter
                         (fun (_, var, tp) ->
                           Env.add_to_internal_env env var (Env.Opaque tp))
                         args2
                     in
                     let res = equiv t1 t2 env in
                     let _ =
                       List.iter
                         (fun (_, var, _) -> Env.rm_from_internal_env env var)
                         args1
                     in
                     let _ =
                       List.iter
                         (fun (_, var, _) -> Env.rm_from_internal_env env var)
                         args2
                     in
                     res
                   else false
               | _ -> false)
             true
             (List.combine branches1 branches2)
      in
      eq_scrut_types && eq_res_types && eq_branches
  | Subst (_, var1, tp1, t1, t2, t3), Subst (_, var2, tp2, t4, t5, t6) ->
      let _ = Env.add_to_internal_env env var1 (Env.Opaque tp1) in
      let _ = Env.add_to_internal_env env var2 (Env.Opaque tp2) in
      let res = equiv t1 t4 env && equiv t2 t5 env && equiv t3 t6 env in
      let _ = Env.rm_from_internal_env env var1 in
      let _ = Env.rm_from_internal_env env var2 in
      res
  | _ ->
      (* Terms are not equivalent *)
      false

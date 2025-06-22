(** [to_whnf t env] converts a term [t] to its weak head normal form (WHNF) in
    the context of environment [env].

    @param t The term to convert to WHNF.
    @param env The term environment.
    @return The WHNF form of [t].
    @raise Failure
      If an error occurs during conversion, raises a failure with an appropriate
      error message. *)
let rec to_whnf (t : Core.term) (env : Env.internal) : Core.whnf =
  match t with
  | Type -> Type
  | Kind -> Kind
  | IntType -> IntType
  | StringType -> StringType
  | BoolType -> BoolType
  | IntLit n -> IntLit n
  | StringLit s -> StringLit s
  | BoolLit s -> BoolLit s
  | Var (nm, x) -> (
      match Env.find_opt_in_internal_env env x with
      | Some (Opaque _) ->
          (* Variable is opaque (e.g., a constant or parameter); cannot reduce further *)
          Neu (nm, x, [])
      | Some (Transparent (body, _)) ->
          (* Variable is transparent (e.g., a let-bound variable); expand its definition *)
          to_whnf body env
      | None ->
          Error.create_whnf_error t env
            ("Couldn't find Variable " ^ nm ^ " " ^ Core.Var.to_string x
           ^ " in environment"))
  | Lambda (nm, x, x_tp, body) -> Lambda (nm, x, x_tp, body)
  | Product (nm, x, x_tp, body) -> Product (nm, x, x_tp, body)
  | TypeArrow (tp1, tp2) ->
      (* Type arrow is syntactic sugar for a product type without a parameter name *)
      Product ("", Core.Var.dummy_var, tp1, tp2)
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
          to_whnf
            (Substitution.substitute body (Substitution.singleton_sub_map x t2))
            env
      | FixNeu
          (fn_nm, fn_var, args, arg, arg_var, arg_tp, body_tp, body, arg_list)
        ->
          begin match args with 
          | (_, var, _) :: args ->
            assert (List.is_empty arg_list);
            let sub_map = Substitution.singleton_sub_map var t2 in
            let args' = List.map (fun (nm, v, tp) -> (nm, v, Substitution.substitute tp sub_map)) args in
            let arg_tp' = Substitution.substitute arg_tp sub_map in 
            let body_tp' = Substitution.substitute body_tp sub_map in 
            let body' = Substitution.substitute body sub_map in 
            FixNeu
            ( fn_nm,
              fn_var,
              args',
              arg,
              arg_var,
              arg_tp',
              body_tp',
              body',
              arg_list )
          | [] ->  
            FixNeu
              ( fn_nm,
                fn_var,
                args,
                arg,
                arg_var,
                arg_tp,
                body_tp,
                body,
                t2 :: arg_list )
        end
      | whnf_term ->
          Error.create_whnf_error t env
            ("When reducing Application expected Neu or Lambda\n" ^ "Got "
            ^ PrettyPrinter.whnf_to_string whnf_term
            ^ " instead"))
  | Hole (nm, tp) ->
      (* A hole is treated as a neutral term with a hole *)
      Neu_with_Hole (nm, tp, [])
  | Let (_, var, t1, _, t2) ->
      (* Let-binding 'let nm = t1 in t2' *)
      to_whnf
        (Substitution.substitute t2 (Substitution.singleton_sub_map var t1))
        env
  | Case (scrut, scrut_tp, maybe_var, tp, branches) -> (
      let scrut_whnf = to_whnf scrut env in
      match scrut_whnf with
      | Neu (nm, _, rev_args) -> (
          match
            List.find_opt
              (function
                | Core.PatCon (dataCName, _), _ ->
                    Core.dataCName_to_string dataCName = nm
                | PatWild, _ -> false)
              branches
          with
          | Some (pattern, term) -> (
              match pattern with
              | PatWild -> failwith "Impossible"
              | PatCon (_, args) ->
                  let sub_map =
                    List.fold_left
                      (fun acc ((_, var, _), term) ->
                        Substitution.add_to_sub_map var term acc)
                      Substitution.empty_sub_map
                      (List.combine args (List.rev rev_args))
                  in
                  let term = Substitution.substitute term sub_map in

                  let whnf_term =
                    match maybe_var with
                    | Some (nm, var) ->
                        let fresh_var = Env.fresh_var () in
                        let _ =
                          Env.add_to_internal_env env fresh_var
                            (Transparent (scrut, scrut_tp))
                        in
                        let term_whnf =
                          to_whnf
                            (Substitution.substitute term
                               (Substitution.singleton_sub_map var
                                  (Core.Var (nm, fresh_var))))
                            env
                        in
                        let _ = Env.rm_from_internal_env env fresh_var in
                        term_whnf
                    | None -> to_whnf term env
                  in
                  whnf_term)
          | None -> Case (scrut, scrut_tp, maybe_var, tp, branches))
      | _ -> Case (scrut, scrut_tp, maybe_var, tp, branches))
  | IfExpr (t, b1, b2) -> (
      let t = to_whnf t env in
      match t with
      | BoolLit b -> if b then to_whnf b1 env else to_whnf b2 env
      | _ -> IfExpr (t, b1, b2))
  | EqType (t1, t2, tp) -> EqType (t1, t2, tp)
  | Refl (t, tp) -> Refl (t, tp)
  | Subst (nm, var, tp, t1, t2, t3) -> (
      let t2_whnf = to_whnf t2 env in
      match t2_whnf with
      | Refl _ -> to_whnf t3 env
      | _ -> Subst (nm, var, tp, t1, t2, t3))
  | FixDef (nm, nm_var, args, arg_nm, arg_var, arg_tp, body_tp, body) ->
      FixNeu (nm, nm_var, args, arg_nm, arg_var, arg_tp, body_tp, body, [])

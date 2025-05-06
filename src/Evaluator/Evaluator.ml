let find_matching_matchPat (nm : string) (patterns : Core.branch list) :
    Core.branch =
  List.find
    (fun (pattern, _) ->
      match pattern with
      | Core.PatCon (dataCName, _) -> nm = Core.dataCName_to_string dataCName
      | Core.PatWild -> true)
    patterns

let add_pattern_vars_to_termEnv (vars : (string * Core.Var.t) list)
    (values : Core.term list) (env : Env.internal) :
    (string * Core.Var.t * Core.Var.t) list =
  let _ = assert (List.length vars == List.length values) in
  List.fold_left
    (fun acc ((nm, var), term) ->
      let fresh_var = Env.fresh_var () in
      let _ = Env.add_to_internal_env env fresh_var (Transparent (term, Type)) in
      (nm, var, fresh_var) :: acc)
    [] (List.combine vars values)

let rm_pattern_vars_to_termEnv
    (bindings : (string * Core.Var.t * Core.Var.t) list) (env : Env.internal) :
    unit =
  List.iter (fun (_, _, x) -> Env.rm_from_internal_env env x) bindings

(** [whnf_to_nf w env] fully normalizes a [whnf] node [w] in context [env],
    producing a [term] in normal form. *)
let rec whnf_to_nf (w : Core.whnf) (env : Env.internal) : Core.term =
  match w with
  | Type ->
      (* Already a normal form. *)
      Type
  | Kind ->
      (* Already a normal form (although 'Kind' doesn't usually appear at runtime). *)
      Kind
  | IntType ->
      (* Already a normal form. *)
      IntType
  | StringType ->
      (* Already a normal form. *)
      StringType
  | BoolType ->
      (* Already a normal form. *)
      BoolType
  | IntLit n ->
      (* Already a normal form. *)
      IntLit n
  | StringLit s ->
      (* Already a normal form. *)
      StringLit s
  | BoolLit b ->
      (* Already a normal form. *)
      BoolLit b
  | Neu (nm, x, rev_args) -> (
      (* Neutral term applied to [rev_args]. Recall that rev_args is stored in reverse. *)
      let nf_args = List.map (fun arg -> eval arg env) (List.rev rev_args) in
      let try_eval_builtin = BuiltIn.eval_builtin nm (Neu (nm, x, nf_args)) in
      match try_eval_builtin with
      | Some nf -> nf
      | None ->
          (* Rebuild as a normal form: Var(...) applied to each argument in the correct order. *)
          List.fold_left
            (fun acc arg -> Core.App (acc, arg))
            (Core.Var (nm, x))
            nf_args)
  | Neu_with_Hole (nm, hole_tp, rev_args) ->
      (* A hole can still appear in normal forms, but we recursively evaluate
         the hole type and arguments, to produce a normal form. *)
      let nf_tp = eval hole_tp env in
      let nf_args = List.map (fun arg -> eval arg env) (List.rev rev_args) in
      let hole = Core.Hole (nm, nf_tp) in
      List.fold_left (fun acc arg -> Core.App (acc, arg)) hole nf_args
  | Lambda (nm, x, tp, body) ->
      (* Generate a fresh variable identifier *)
      let fresh_var = Env.fresh_var () in
      (* Add the definition of 'tp' to the environment with the fresh variable *)
      Env.add_to_internal_env env fresh_var (Opaque tp);
      (* Evaluate type and body *)
      let nf_tp =
        eval
          (TypeChecker.Substitution.substitute tp
             (TypeChecker.Substitution.singleton_sub_map x
                (Core.Var (nm, fresh_var))))
          env
      in
      let nf_body =
        eval
          (TypeChecker.Substitution.substitute body
             (TypeChecker.Substitution.singleton_sub_map x
                (Core.Var (nm, fresh_var))))
          env
      in
      (* Remove the fresh variable from the environment *)
      Env.rm_from_internal_env env fresh_var;
      (* Return the normalized lambda *)
      Lambda (nm, fresh_var, nf_tp, nf_body)
  | Product (nm, x, tp, body) ->
      if Core.Var.equal x (Core.Var.of_int (-1)) then
        let nf_tp = eval tp env in
        let nf_body = eval body env in
        TypeArrow (nf_tp, nf_body)
      else
        (* Generate a fresh variable identifier *)
        let fresh_var = Env.fresh_var () in
        (* Add the definition of 'tp' to the environment with the fresh variable *)
        Env.add_to_internal_env env fresh_var (Opaque tp);
        (* Evaluate type and body *)
        let nf_tp =
          eval
            (TypeChecker.Substitution.substitute tp
               (TypeChecker.Substitution.singleton_sub_map x
                  (Core.Var (nm, fresh_var))))
            env
        in
        let nf_body =
          eval
            (TypeChecker.Substitution.substitute body
               (TypeChecker.Substitution.singleton_sub_map x
                  (Core.Var (nm, fresh_var))))
            env
        in
        (* Remove the fresh variable from the environment *)
        Env.rm_from_internal_env env fresh_var;
        (* Return the normalized product *)
        Product (nm, fresh_var, nf_tp, nf_body)
  | Case (scrutinee, patterns) -> (
      match scrutinee with
      | Neu (nm, _, rev_args) -> (
          let pattern, term = find_matching_matchPat nm patterns in
          match pattern with
          | PatWild -> eval term env
          | PatCon (_, args) ->
              let bindings =
                add_pattern_vars_to_termEnv args (List.rev rev_args) env
              in
              let sub_map =
                List.fold_left
                  (fun acc (nm, var, fresh_var) ->
                    TypeChecker.Substitution.add_to_sub_map var
                      (Var (nm, fresh_var))
                      acc)
                  TypeChecker.Substitution.empty_sub_map bindings
              in
              let nf_term =
                eval (TypeChecker.Substitution.substitute term sub_map) env
              in
              let _ = rm_pattern_vars_to_termEnv bindings env in
              nf_term)
      | _ ->
          failwith "RUNTIME ERROR while evaluating Case, scrutinee is not Neu.")
  | IfExpr (t, b1, b2) -> (
      match whnf_to_nf t env with
      | BoolLit b -> if b then eval b1 env else eval b2 env
      | _ as t ->
          if TypeChecker.Equiv.equiv b1 b2 env then b1 else IfExpr (t, b1, b2))
  | Equality (t1, t2) -> (
      let t1 = eval t1 env in
      let t2 = eval t2 env in
      match TypeChecker.Equiv.equiv_optional t1 t2 env with
      | Some b -> BoolLit b
      | None -> Equality (t1, t2))

and eval (t : Core.term) (env : Env.internal) : Core.term =
  let w = TypeChecker.Whnf.to_whnf t env in
  whnf_to_nf w env

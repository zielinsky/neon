let find_matching_matchPat (nm : string) (patterns : Core.branch list) :
    Core.branch =
  List.find
    (fun (pattern, _) ->
      match pattern with
      | Core.PatCon (dataCName, _) -> nm = Core.dataCName_to_string dataCName
      | Core.PatWild -> true)
    patterns

(** [whnf_to_nf w env] fully normalizes a [whnf] node [w] in context [env],
    producing a [term] in normal form. *)
let rec whnf_to_nf (w : Core.whnf) (env : Env.internal) : Core.term =
  (* Print the current term being normalized for debugging purposes. *)
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
  | Lambda (nm, x, tp, body) -> Lambda (nm, x, tp, body)
  | Product (nm, x, tp, body) ->
      if Core.Var.equal x (Core.Var.of_int (-1)) then
        let nf_tp = eval tp env in
        let nf_body = eval body env in
        TypeArrow (nf_tp, nf_body)
      else Product (nm, x, tp, body)
  | Case (scrutinee, _, _, _, patterns) -> (
      match scrutinee with
      | Neu (nm, _, rev_args) -> (
          let pattern, term = find_matching_matchPat nm patterns in
          match pattern with
          | PatWild -> eval term env
          | PatCon (_, args) ->
              let sub_map =
                List.fold_left
                  (fun acc ((_, var, _), term) ->
                    TypeChecker.Substitution.add_to_sub_map var term acc)
                  TypeChecker.Substitution.empty_sub_map
                  (List.combine args (List.rev rev_args))
              in
              let nf_term =
                eval (TypeChecker.Substitution.substitute term sub_map) env
              in
              nf_term)
      | _ ->
          failwith "RUNTIME ERROR while evaluating Case, scrutinee is not Neu.")
  | IfExpr (t, b1, b2) -> (
      match whnf_to_nf t env with
      | BoolLit b -> if b then eval b1 env else eval b2 env
      | _ as t ->
          if TypeChecker.Equiv.equiv b1 b2 env then b1 else IfExpr (t, b1, b2))
  | EqType (t1, t2, tp) -> EqType (t1, t2, tp)
  | Refl (t, tp) -> Refl (t, tp)
  | Subst (nm, var, tp, t1, t2, t3) -> Subst (nm, var, tp, t1, t2, t3)
  | FixDef (fn_nm, fn_var, dep_args, arg, arg_var, arg_tp, body_tp, body) ->
      FixDef (fn_nm, fn_var, dep_args, arg, arg_var, arg_tp, body_tp, body)

and eval (t : Core.term) (env : Env.internal) : Core.term =
  let w = TypeChecker.Whnf.to_whnf t env in
  whnf_to_nf w env

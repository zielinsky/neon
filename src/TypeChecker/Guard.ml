module VS = Set.Make (struct
  type t = Core.Var.t

  let compare = Core.Var.compare
end)

let vars_of_pattern : Core.pattern -> VS.t = function
  | PatWild -> VS.empty
  | PatCon (_, xs) ->
      List.fold_left (fun acc (_, v) -> VS.add v acc) VS.empty xs

type ctx = {
  matched : bool; (* If were in a branch after matching on arg_var? *)
  allowed : VS.t; (* Variables that are allowed in the argument *)
}

let rec traverse (fn_var : Core.Var.t) (arg_var : Core.Var.t) (arg_pos : int)
    (ctx : ctx) (env : Env.internal) (t : Core.term) : unit =
  match t with
  | App (t1, t2) as app -> (
      match Whnf.to_whnf app env with
      | Neu (_, v_fn, rev_args) when Core.Var.equal v_fn fn_var -> (
          let args = List.rev rev_args in
          if List.length args <= arg_pos then
            failwith "[Guard] Not enough arguments in the application";
          let dec_arg = List.nth args arg_pos in
          if not ctx.matched then
            failwith
              "[Guard] Application before matching on a structure argument";
          if OccursCheck.occurs_check_term arg_var dec_arg then
            failwith "[Guard] Recursion does not allow self-reference";
          match Whnf.to_whnf dec_arg env with
          | Neu (_, v_arg, _) ->
              if not (VS.mem v_arg ctx.allowed) then
                failwith "[Guard] Recursion on a variable that is not allowed";
              ()
          | _ -> failwith "[Guard] Recursion on a non-variable argument")
      | _ ->
          traverse fn_var arg_var arg_pos ctx env t1;
          traverse fn_var arg_var arg_pos ctx env t2)
  | Lambda (_, var, var_tp, body) ->
      Env.add_to_internal_env env var (Opaque var_tp);
      traverse fn_var arg_var arg_pos ctx env body;
      Env.rm_from_internal_env env var
  | Product (_, var, tp, body) ->
      Env.add_to_internal_env env var (Opaque tp);
      traverse fn_var arg_var arg_pos ctx env tp;
      traverse fn_var arg_var arg_pos ctx env body;
      Env.rm_from_internal_env env var
  | TypeArrow (tp1, tp2) ->
      traverse fn_var arg_var arg_pos ctx env tp1;
      traverse fn_var arg_var arg_pos ctx env tp2
  | Let (_, var, t1, tp, t2) ->
      Env.add_to_internal_env env var (Transparent (t1, tp));
      traverse fn_var arg_var arg_pos ctx env t1;
      traverse fn_var arg_var arg_pos ctx env tp;
      traverse fn_var arg_var arg_pos ctx env t2;
      Env.rm_from_internal_env env var
  | Case (scrut, _, _, _, branches) ->
      traverse fn_var arg_var arg_pos ctx env scrut;
      let is_on_arg =
        match scrut with
        | Var (_, v) when Core.Var.equal v arg_var -> true
        | _ -> false
      in
      List.iter
        (fun (pat, br_body) ->
          let allowed' =
            if is_on_arg then VS.union ctx.allowed (vars_of_pattern pat)
            else ctx.allowed
          in
          let ctx' =
            { matched = ctx.matched || is_on_arg; allowed = allowed' }
          in
          traverse fn_var arg_var arg_pos ctx' env br_body)
        branches
  | IfExpr (c, t1, t2) ->
      traverse fn_var arg_var arg_pos ctx env c;
      traverse fn_var arg_var arg_pos ctx env t1;
      traverse fn_var arg_var arg_pos ctx env t2
  | EqType (t1, t2, tp) ->
      traverse fn_var arg_var arg_pos ctx env t1;
      traverse fn_var arg_var arg_pos ctx env t2;
      traverse fn_var arg_var arg_pos ctx env tp
  | Refl (t1, tp) ->
      traverse fn_var arg_var arg_pos ctx env t1;
      traverse fn_var arg_var arg_pos ctx env tp
  | Subst (_, _, t1, t2, t3) ->
      traverse fn_var arg_var arg_pos ctx env t1;
      traverse fn_var arg_var arg_pos ctx env t2;
      traverse fn_var arg_var arg_pos ctx env t3
  | Hole _ | Type | Kind | IntType | StringType | BoolType | IntLit _
  | StringLit _ | BoolLit _ | Var _ ->
      ()

let check_totality (fn_var : Core.Var.t) (arg_var : Core.Var.t) (arg_pos : int)
    (body : Core.term) (env : Env.internal) : unit =
  try
    let init = { matched = false; allowed = VS.empty } in
    traverse fn_var arg_var arg_pos init env body
  with Failure msg ->
    raise (Failure ("[Guard] totality check failed: " ^ msg))

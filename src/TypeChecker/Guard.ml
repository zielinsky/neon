module VS = Set.Make (struct
  type t = Core.Var.t

  let compare = Core.Var.compare
end)

let vars_of_pattern : Core.pattern -> VS.t = function
  | PatWild -> VS.empty
  | PatCon (_, xs) ->
      List.fold_left (fun acc (_, v, _) -> VS.add v acc) VS.empty xs

type ctx = { allowed : VS.t (* Variables that are allowed in the argument *) }

let rec traverse (fn_var : Core.Var.t) (arg_var : Core.Var.t) (arg_pos : int)
    (ctx : ctx) (env : Env.internal) (t : Core.term) : unit =
  match t with
  | App (t1, t2) as app -> (
      match Whnf.to_whnf app env with
      | Neu (_, v_fn, rev_args) when Core.Var.equal v_fn fn_var -> (
          let args = List.rev rev_args in
          let _ = print_endline "Checking application of fix" in
          let _ =
            List.iter
              (fun x -> print_endline (PrettyPrinter.term_to_string x))
              args
          in
          if List.length args <= arg_pos then
            failwith "Not enough arguments in the application";
          let dec_arg = List.nth args arg_pos in
          if VS.is_empty ctx.allowed then
            failwith "Application before matching on a structure argument";
          match Whnf.to_whnf dec_arg env with
          | Neu (_, v_arg, _) ->
              if not (VS.mem v_arg ctx.allowed) then
                failwith "Recursion on a variable that is not allowed";
              List.iter
                (fun t -> traverse fn_var arg_var arg_pos ctx env t)
                rev_args
          | _ -> failwith "Recursion on a non-variable argument")
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
          let _ = Env.add_pattern_to_internal_env env pat in
          let allowed' =
            if is_on_arg then VS.union ctx.allowed (vars_of_pattern pat)
            else ctx.allowed
          in
          let ctx' = { allowed = allowed' } in
          traverse fn_var arg_var arg_pos ctx' env br_body;
          Env.rm_pattern_from_internal_env env pat)
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
  | Subst (_, _, tp, t1, t2, t3) ->
      traverse fn_var arg_var arg_pos ctx env tp;
      traverse fn_var arg_var arg_pos ctx env t1;
      traverse fn_var arg_var arg_pos ctx env t2;
      traverse fn_var arg_var arg_pos ctx env t3
  | Hole _ | Type | Kind | IntType | StringType | BoolType | IntLit _
  | StringLit _ | BoolLit _ | Var _ ->
      ()

let check_totality (fn_var : Core.Var.t) (arg_var : Core.Var.t) (arg_pos : int)
    (body : Core.term) (env : Env.internal) : unit =
  try
    let init = { allowed = VS.empty } in
    traverse fn_var arg_var arg_pos init env body
  with Failure msg -> Error.create_guard_error msg body

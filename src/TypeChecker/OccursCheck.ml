let rec occurs_check_whnf (var : Core.Var.t) (whnf_term : Core.whnf) : bool =
  match whnf_term with
  | Type | Kind | IntType | StringType | BoolType | IntLit _ | StringLit _
  | BoolLit _ ->
      false
  | Neu (_, x, args) ->
      Core.Var.equal var x || List.exists (occurs_check_term var) args
  | Neu_with_Hole (_, tp, args) ->
      occurs_check_term var tp || List.exists (occurs_check_term var) args
  | Lambda (_, _, x_tp, body) ->
      occurs_check_term var x_tp || occurs_check_term var body
  | Product (_, _, x_tp, body_tp) ->
      occurs_check_term var x_tp || occurs_check_term var body_tp
  | Case (scrutinee, scrutinee_tp, as_var, tp, branches) ->
      occurs_check_whnf var scrutinee
      || occurs_check_term var scrutinee_tp
      || (match as_var with
         | Some (_, x) -> Core.Var.equal var x
         | None -> false)
      || occurs_check_term var tp
      || List.exists (fun (_, body) -> occurs_check_term var body) branches
  | IfExpr (t, b1, b2) ->
      occurs_check_whnf var t || occurs_check_term var b1
      || occurs_check_term var b2
  | EqType (t1, t2, tp) ->
      occurs_check_term var t1 || occurs_check_term var t2
      || occurs_check_term var tp
  | Refl (t, tp) -> occurs_check_term var t || occurs_check_term var tp
  | Subst (_, x, t1, t2, t3) ->
      Core.Var.equal var x || occurs_check_term var t1
      || occurs_check_whnf var t2 || occurs_check_term var t3

and occurs_check_term (var : Core.Var.t) (term : Core.term) : bool =
  match term with
  | Type | Kind | IntType | StringType | BoolType | IntLit _ | StringLit _
  | BoolLit _ ->
      false
  | Var (_, x) -> Core.Var.equal var x
  | Lambda (_, _, x_tp, body) ->
      occurs_check_term var x_tp || occurs_check_term var body
  | Product (_, _, x_tp, body_tp) ->
      occurs_check_term var x_tp || occurs_check_term var body_tp
  | App (t1, t2) -> occurs_check_term var t1 || occurs_check_term var t2
  | Hole (_, tp) -> occurs_check_term var tp
  | Let (_, _, t1, tp_t1, t2) ->
      occurs_check_term var t1
      || occurs_check_term var tp_t1
      || occurs_check_term var t2
  | TypeArrow (tp1, tp2) ->
      occurs_check_term var tp1 || occurs_check_term var tp2
  | Case (scrutinee, scrutinee_tp, as_var, tp, branches) ->
      occurs_check_term var scrutinee
      || occurs_check_term var scrutinee_tp
      || (match as_var with
         | Some (_, x) -> Core.Var.equal var x
         | None -> false)
      || occurs_check_term var tp
      || List.exists (fun (_, body) -> occurs_check_term var body) branches
  | IfExpr (t, b1, b2) ->
      occurs_check_term var t || occurs_check_term var b1
      || occurs_check_term var b2
  | EqType (t1, t2, tp) ->
      occurs_check_term var t1 || occurs_check_term var t2
      || occurs_check_term var tp
  | Refl (t, tp) -> occurs_check_term var t || occurs_check_term var tp
  | Subst (_, x, t1, t2, t3) ->
      Core.Var.equal var x || occurs_check_term var t1
      || occurs_check_term var t2 || occurs_check_term var t3

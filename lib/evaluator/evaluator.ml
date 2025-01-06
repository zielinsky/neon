open TypeChecker
open Ast
open Env

(** [whnf_to_nf w env] fully normalizes a [whnf] node [w] in context [env],
producing a [term] in normal form. *)
let rec whnf_to_nf (w : whnf) (env : termEnv) : term =
  match w with
  | IntType | StringType | BoolType | IntLit _ | StringLit _ | BoolLit _ ->
      (match w with
       | IntType -> IntType
       | StringType -> StringType
       | BoolType -> BoolType
       | IntLit n -> IntLit n
       | StringLit s -> StringLit s
       | BoolLit b -> BoolLit b
       | _ -> failwith "Unexpected case")
  | Type ->
      (* Already a normal form. *)
      Type
  | Kind ->
      (* Already a normal form (although 'Kind' doesn't usually appear at runtime). *)
      Kind
  | Neu (nm, x, rev_args) ->
      (* Neutral term applied to [rev_args]. Recall that rev_args is stored in reverse. *)
      let nf_args =
        List.map (fun arg -> eval arg env) (List.rev rev_args)
      in
      (* Rebuild as a normal form: Var(...) applied to each argument in the correct order. *)
      List.fold_left (fun acc arg -> App (acc, arg)) (Var (nm, x)) nf_args
  
  | Neu_with_Hole (nm, hole_tp, rev_args) ->
      (* A hole can still appear in normal forms, but we recursively evaluate
         the hole type and arguments, to produce a normal form. *)
      let nf_tp = eval hole_tp env in
      let nf_args =
        List.map (fun arg -> eval arg env) (List.rev rev_args)
      in
      let hole = Hole (nm, nf_tp) in
      List.fold_left (fun acc arg -> App (acc, arg)) hole nf_args
  
  | Lambda (nm, x, tp, body) ->
    (* Generate a fresh variable identifier *)
    let fresh_var = fresh_var () in
    (* Add the definition of 'tp' to the environment with the fresh variable *)
    add_to_termEnv env fresh_var (Opaque tp);
    (* Evaluate type and body *)
    let nf_tp   = eval (substitute tp (VarMap.singleton x (Var (nm, fresh_var)))) env in
    let nf_body = eval (substitute body (VarMap.singleton x (Var (nm, fresh_var)))) env in
    (* Remove the fresh variable from the environment *)
    rm_from_termEnv env fresh_var;
    (* Return the normalized lambda *)
    Lambda (nm, fresh_var, nf_tp, nf_body)

  | Product (nm, x, tp, body) ->
    (* Generate a fresh variable identifier *)
    let fresh_var = fresh_var () in
    (* Add the definition of 'tp' to the environment with the fresh variable *)
    add_to_termEnv env fresh_var (Opaque tp);
    (* Evaluate type and body *)
    let nf_tp   = eval (substitute tp (VarMap.singleton x (Var (nm, fresh_var)))) env in
    let nf_body = eval (substitute body (VarMap.singleton x (Var (nm, fresh_var)))) env in
    (* Remove the fresh variable from the environment *)
    rm_from_termEnv env fresh_var;
    (* Return the normalized product *)
    Product (nm, fresh_var, nf_tp, nf_body)
and eval (t : term) (env : termEnv) : term =
  let w = to_whnf t env in
  whnf_to_nf w env
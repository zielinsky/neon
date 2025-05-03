open TypeChecker
open Ast
open Env
open BuiltIn

let find_matching_matchPat (nm : string) (patterns : matchPat list) : matchPat =
  List.find
    (fun (pattern, _) ->
      match pattern with
      | PatCon (dataCName, _) -> nm = dataCName
      | PatWild -> true)
    patterns

let add_pattern_vars_to_termEnv (vars : (string * var) list)
    (values : term list) (env : termEnv) : (string * var * var) list =
  let _ = assert (List.length vars == List.length values) in
  List.fold_left
    (fun acc ((nm, var), term) ->
      let fresh_var = fresh_var () in
      let _ = add_to_termEnv env fresh_var (Transparent (term, Type)) in
      (nm, var, fresh_var) :: acc)
    [] (List.combine vars values)

let rm_pattern_vars_to_termEnv (bindings : (string * var * var) list)
    (env : termEnv) : unit =
  List.iter (fun (_, _, x) -> rm_from_termEnv env x) bindings

(** [whnf_to_nf w env] fully normalizes a [whnf] node [w] in context [env],
    producing a [term] in normal form. *)
let rec whnf_to_nf (w : whnf) (env : termEnv) : term =
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
      let try_eval_builtin = eval_builtin nm (Neu (nm, x, nf_args)) in
      match try_eval_builtin with
      | Some nf -> nf
      | None ->
          (* Rebuild as a normal form: Var(...) applied to each argument in the correct order. *)
          List.fold_left (fun acc arg -> App (acc, arg)) (Var (nm, x)) nf_args)
  | Neu_with_Hole (nm, hole_tp, rev_args) ->
      (* A hole can still appear in normal forms, but we recursively evaluate
         the hole type and arguments, to produce a normal form. *)
      let nf_tp = eval hole_tp env in
      let nf_args = List.map (fun arg -> eval arg env) (List.rev rev_args) in
      let hole = Hole (nm, nf_tp) in
      List.fold_left (fun acc arg -> App (acc, arg)) hole nf_args
  | Lambda (nm, x, tp, body) ->
      (* Generate a fresh variable identifier *)
      let fresh_var = fresh_var () in
      (* Add the definition of 'tp' to the environment with the fresh variable *)
      add_to_termEnv env fresh_var (Opaque tp);
      (* Evaluate type and body *)
      let nf_tp =
        eval (substitute tp (VarMap.singleton x (Var (nm, fresh_var)))) env
      in
      let nf_body =
        eval (substitute body (VarMap.singleton x (Var (nm, fresh_var)))) env
      in
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
      let nf_tp =
        eval (substitute tp (VarMap.singleton x (Var (nm, fresh_var)))) env
      in
      let nf_body =
        eval (substitute body (VarMap.singleton x (Var (nm, fresh_var)))) env
      in
      (* Remove the fresh variable from the environment *)
      rm_from_termEnv env fresh_var;
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
                    VarMap.add var (Var (nm, fresh_var)) acc)
                  VarMap.empty bindings
              in
              let nf_term = eval (substitute term sub_map) env in
              let _ = rm_pattern_vars_to_termEnv bindings env in
              nf_term)
      | _ ->
          failwith "RUNTIME ERROR while evaluating Case, scrutinee is not Neu.")

and eval (t : term) (env : termEnv) : term =
  let w = to_whnf t env in
  whnf_to_nf w env

module Substitution = Substitution
module Whnf = Whnf
module Equiv = Equiv
module OccursCheck = OccursCheck

let telescope_length (ts : Core.telescope) : int =
  let rec tele_len (ts : Core.telescope) (acc : int) =
    match ts with Empty -> acc | Cons (_, _, _, ts) -> tele_len ts (acc + 1)
  in
  tele_len ts 0

let split_pattern_args (tsT_len : int) (args : string list) :
    string list * string list =
  let rec split_list_at_n (n : int) (xs : 'a list) (acc : 'a list) =
    match (xs, n) with
    | xs, 0 -> (List.rev acc, xs)
    | x :: xs, _ -> split_list_at_n (n - 1) xs (x :: acc)
    | [], _ -> failwith "Unreachable in split_list_at_n"
  in
  let _ = assert (List.length args >= tsT_len) in
  split_list_at_n tsT_len args []

let rec build_adt_sig (env : Env.env) (ts : Core.telescope) : Core.term =
  match ts with
  | Empty -> Type
  | Cons (nm, var, tp, ts) ->
      let res : Core.term = Product (nm, var, tp, build_adt_sig env ts) in
      res

let rec build_adt_data (env : Env.env) (tsType : Core.telescope)
    (tsData : Core.telescope) (var_list : (string * Core.Var.t) list)
    (adt_sig_var : string * Core.Var.t) : Core.term =
  match tsType with
  | Empty -> (
      match tsData with
      | Empty ->
          let adt_nm, adt_var = adt_sig_var in
          List.fold_left
            (fun acc (nm, var) -> Core.App (acc, Var (nm, var)))
            (Core.Var (adt_nm, adt_var))
            (List.rev var_list)
      | Cons (nm, var, tp, ts) ->
          let res : Core.term =
            Product
              (nm, var, tp, build_adt_data env tsType ts var_list adt_sig_var)
          in
          res)
  | Cons (nm, var, tp, ts) ->
      let res : Core.term =
        Product
          ( nm,
            var,
            tp,
            build_adt_data env ts tsData ((nm, var) :: var_list) adt_sig_var )
      in
      res

let check_exhaustivity_and_constructor_names (ps : Raw.branch list)
    (dataCNames : Core.dataCName list) : unit =
  let rec collect_constructor_names (ps : Raw.branch list) :
      Core.dataCName list * bool =
    match ps with
    | (PatCon (dataCName, _), _) :: ps ->
        let cs, contaisWild = collect_constructor_names ps in
        (Core.dataCName_of_string dataCName :: cs, contaisWild)
    | (PatWild, _) :: [] -> ([], true)
    | (PatWild, _) :: _ ->
        failwith "Wild card must be the last branch in pattern matching"
    | [] -> ([], false)
  in
  let cs, containsWild = collect_constructor_names ps in
  (* Check that all collected constructors belong to this ADT and check exhaustivity *)
  if not (List.fold_left (fun acc x -> acc && List.mem x dataCNames) true cs)
  then failwith "Constructor names mismatch in pattern matching branches"
  else if
    not
      ((containsWild && List.compare_lengths cs dataCNames <= 0)
      || ((not containsWild) && List.compare_lengths cs dataCNames == 0))
  then failwith "Exhaustivity check for pattern matching branches failed"

let check_branch_types (env : Env.env) (branch_types : Core.tp list) : unit =
  let hd = List.hd branch_types in
  let _, isSameType =
    List.fold_left
      (fun (prev_tp, cond) tp ->
        (tp, cond && Equiv.equiv prev_tp tp env.internal))
      (hd, true) (List.tl branch_types)
  in
  if isSameType then ()
  else failwith "Pattern matching branches have different types"

let rec subst_and_add_tsT_to_env (env : Env.env) (tsT : Core.telescope)
    (tsT_types : Core.tp list) (argsT : string list) :
    (Core.Var.t * (string * Core.Var.t * Core.tp)) list =
  match tsT with
  | Empty -> []
  | Cons (_, var, tp, tsT) ->
      let concrete_tp = List.hd tsT_types in
      let new_nm = List.hd argsT in
      let fresh_var =
        Env.add_to_env env new_nm (Transparent (concrete_tp, tp))
      in
      (* Changed the substituion: Instead of substituting concrete_tp for the old var
         we pass newly create Var instead. ASK PPO *)
      let tsT =
        Substitution.substitute_in_telescope tsT
          (Substitution.singleton_sub_map var (Core.Var (new_nm, fresh_var)))
        (* let tsT =
        Substitution.substitute_in_telescope tsT
          (Substitution.singleton_sub_map var concrete_tp) *)
      in
      (var, (new_nm, fresh_var, tp))
      :: subst_and_add_tsT_to_env env tsT (List.tl tsT_types) (List.tl argsT)

let rec subs_and_add_tsD_to_env (env : Env.env) (tsD : Core.telescope)
    (argsD : string list) : (string * Core.Var.t * Core.tp) list =
  match tsD with
  | Empty -> []
  | Cons (_, var, tp, tsD) ->
      let new_nm = List.hd argsD in
      let fresh_var = Env.add_to_env env new_nm (Opaque tp) in
      let tsD =
        Substitution.substitute_in_telescope tsD
          (Substitution.singleton_sub_map var (Core.Var (new_nm, fresh_var)))
      in
      (new_nm, fresh_var, tp) :: subs_and_add_tsD_to_env env tsD (List.tl argsD)

let extend_branch_env (env : Env.env) (tsT : Core.telescope)
    (tsT_types : Core.tp list) (tsD : Core.telescope) (args : string list)
    ({ pos; _ } as term : Raw.term) :
    (string * Core.Var.t * Core.tp) list * (string * Core.Var.t * Core.tp) list
    =
  if telescope_length tsT + telescope_length tsD = List.length args then
    let argsT, argsD = split_pattern_args (telescope_length tsT) args in
    let tsT_all_vars = subst_and_add_tsT_to_env env tsT tsT_types argsT in
    let tsD =
      Substitution.substitute_in_telescope tsD
        (Substitution.of_list_sub_map
           (List.combine (fst (List.split tsT_all_vars)) tsT_types))
    in
    let tsD_all_vars = subs_and_add_tsD_to_env env tsD argsD in
    (snd (List.split tsT_all_vars), tsD_all_vars)
  else
    Error.create_infer_type_error pos
      "The number of arguments in branch's pattern must match the telescope"
      term env

let purge_branch_surface_env (env : Env.env)
    (vars : (string * Core.Var.t * Core.tp) list) : unit =
  let names = List.map (fun (nm, _, _) -> nm) vars in
  List.iter (fun nm -> Env.rm_from_surface_env env.surface nm) names

let purge_branch_env (env : Env.env)
    (vars : (string * Core.Var.t * Core.tp) list) : unit =
  let names = List.map (fun (nm, _, _) -> nm) vars in
  List.iter (fun nm -> Env.rm_from_env env nm) names

let purge_all_branches_internal_env (env : Env.env)
    (vars : (string * Core.Var.t * Core.tp) list list) : unit =
  let internal_vars = List.map (fun (_, var, _) -> var) (List.flatten vars) in
  List.iter (fun var -> Env.rm_from_internal_env env.internal var) internal_vars

(** [infer_type env term] infers the type of the given term [term] in the
    context of environment [env].

    @param env The environment containing variable and term bindings.
    @param term The term for which to infer the type.
    @return
      A pair [(t, tp)] where [t] is the term with variables resolved, and [tp]
      is the inferred type of [t].
    @raise Failure
      If type inference fails, raises an exception with an appropriate error
      message. *)
let rec infer_type (env : Env.env) ({ pos; data = t } as term : Raw.term) :
    Core.term * Core.tp =
  match t with
  | Type -> (Type, Kind)
  | Kind ->
      Error.create_infer_type_error pos "Can't infer the type of Kind" term env
  | IntType -> (IntType, Type)
  | StringType -> (StringType, Type)
  | BoolType -> (BoolType, Type)
  | IntLit n -> (IntLit n, IntType)
  | StringLit s -> (StringLit s, StringType)
  | BoolLit b -> (BoolLit b, BoolType)
  | Var x -> (
      match Env.find_opt_in_env env x with
      | Some (y, (Opaque tp | Transparent (_, tp))) -> (Var (x, y), tp)
      | None ->
          Error.create_infer_type_error pos
            ("Variable " ^ x ^ " not found")
            term env)
  | Lambda (_, None, _) ->
      (* Lambda expression with omitted argument type *)
      Error.create_infer_type_error pos
        "Can't infer the type of lambda with omitted argument type" term env
  | Lambda (x, Some tp, t) -> (
      (* Lambda with argument name 'x', argument type 'tp', and body 't' *)
      let tp, tp_of_tp = infer_type env tp in
      match tp_of_tp with
      | Type | Kind ->
          let fresh_var = Env.add_to_env env x (Opaque tp) in
          let body, body_tp = infer_type env t in
          let is_dependent = OccursCheck.occurs_check_term fresh_var body_tp in
          let _ = Env.rm_from_env env x in
          if is_dependent then
            ( Lambda (x, fresh_var, tp, body),
              Product (x, fresh_var, tp, body_tp) )
          else (Lambda (x, fresh_var, tp, body), TypeArrow (tp, body_tp))
      | _ ->
          Error.create_infer_type_error pos
            "The type of Lambda argument type must be either Type or Kind" term
            env)
  | Product (x, tp, t) -> (
      (* Product type with parameter 'x', parameter type 'tp', and body 't' *)
      let tp, tp_of_tp = infer_type env tp in
      match tp_of_tp with
      | Type | Kind -> (
          let fresh_var = Env.add_to_env env x (Opaque tp) in
          let body, body_tp = infer_type env t in
          let _ = Env.rm_from_env env x in
          match body_tp with
          | Type | Kind -> (Product (x, fresh_var, tp, body), body_tp)
          | _ ->
              Error.create_infer_type_error pos
                "The type of Product body type must be either Type or Kind" term
                env)
      | _ ->
          Error.create_infer_type_error pos
            "The type of Product argument type must be either Type or Kind" term
            env)
  | TypeArrow (tp1, tp2) -> (
      (* Function type arrow from 'tp1' to 'tp2' *)
      let tp1, tp_of_tp1 = infer_type env tp1 in
      match tp_of_tp1 with
      | Type | Kind -> (
          let tp2, tp_of_tp2 = infer_type env tp2 in
          match tp_of_tp2 with
          | Type | Kind -> (TypeArrow (tp1, tp2), tp_of_tp2)
          | _ ->
              Error.create_infer_type_error pos
                "The type of Type Arrow body type must be either Type or Kind"
                term env)
      | _ ->
          Error.create_infer_type_error pos
            "The type of Type Arrow argument type must be either Type or Kind"
            term env)
  | App (t1, t2) -> (
      (* Application of function 't1' to argument 't2' *)
      let t1, t1_tp = infer_type env t1 in
      match Whnf.to_whnf t1_tp env.internal with
      | Product (_, x, x_tp, tp_body) ->
          let t2 = check_type env t2 x_tp in
          ( App (t1, t2),
            Substitution.substitute tp_body
              (Substitution.singleton_sub_map x t2) )
      | _ ->
          Error.create_infer_type_error pos
            "The type of Application's first argument must be a Product" term
            env)
  | TermWithTypeAnno (t, tp) -> (
      (* Term 't' with type annotation 'tp' *)
      let tp, tp_of_tp = infer_type env tp in
      match tp_of_tp with
      | Type | Kind -> (check_type env t tp, tp)
      | _ ->
          Error.create_infer_type_error pos
            "Type annotation must be a Type or Kind" term env)
  | Let (x, t1, t2) ->
      (* Let-binding 'let x = t1 in t2' *)
      let t1, tp_t1 = infer_type env t1 in
      let fresh_var = Env.add_to_env env x (Transparent (t1, tp_t1)) in
      let t2, tp_t2 = infer_type env t2 in
      let _ = Env.rm_from_env env x in
      (* The type of the let-binding is 'tp_t2' with 'x' substituted by 't1' *)
      ( Let (x, fresh_var, t1, tp_t1, t2),
        Substitution.substitute tp_t2
          (Substitution.singleton_sub_map fresh_var t1) )
  | LetDef (x, t1) ->
      (* Let-definition 'let x = t1' *)
      let t1, tp_t1 = infer_type env t1 in
      let _ = Env.add_to_env env x (Transparent (t1, tp_t1)) in
      (t1, tp_t1)
  | Lemma (x, t1, t2) ->
      (* Lemma 'lemma x = t1 in t2' *)
      let t1, tp_t1 = infer_type env t1 in
      let fresh_var = Env.add_to_env env x (Opaque tp_t1) in
      let t2, tp_t2 = infer_type env t2 in
      let _ = Env.rm_from_env env x in
      (* Apply the lemma by constructing 'App (Lambda (x, tp_t1, t2), t1)' *)
      ( App (Lambda (x, fresh_var, tp_t1, t2), t1),
        Substitution.substitute tp_t2
          (Substitution.singleton_sub_map fresh_var t1) )
  | LemmaDef (x, t1) ->
      (* Lemma definition 'lemma x = t1' *)
      let t1, tp_t1 = infer_type env t1 in
      let _ = Env.add_to_env env x (Opaque tp_t1) in
      (t1, tp_t1)
  | Hole x ->
      Error.create_infer_type_error pos
        ("Trying to infer the type of a Hole " ^ x)
        term env
  | ADTSig (nm, ts) ->
      let ts' = telescope_check_type_and_extend_env env ts in
      let _ = Env.add_to_adt_env env.adt nm (AdtTSig (ts', [])) in
      let adt_sig_tp = build_adt_sig env ts' in
      let fresh_var = Env.add_to_env env nm (Opaque adt_sig_tp) in
      let _ = Env.rm_telescope_from_env env ts' in
      (Var (nm, fresh_var), adt_sig_tp)
  | ADTDecl (nm, ts, cs) ->
      let ts' = telescope_check_type_and_extend_env env ts in
      let dataCNames =
        List.map
          (fun { Raw.cname = nmCon; _ } -> Core.dataCName_of_string nmCon)
          cs
      in
      let _ = Env.add_to_adt_env env.adt nm (AdtTSig (ts', dataCNames)) in
      let adt_sig_tp = build_adt_sig env ts' in
      let fresh_var = Env.add_to_env env nm (Opaque adt_sig_tp) in
      let con_list =
        List.map
          (fun { Raw.cname = nmCon; Raw.telescope = tsCon } ->
            let tsCon' = telescope_check_type_and_extend_env env tsCon in
            let _ =
              Env.add_to_adt_env env.adt nmCon
                (AdtDSig (Core.typeCName_of_string nm, tsCon'))
            in
            let _ = Env.rm_telescope_from_env env tsCon' in
            { Core.cname = nmCon; Core.telescope = tsCon' })
          cs
      in
      let _ = Env.rm_telescope_from_env env ts' in
      let cs =
        List.map
          (fun (data_con : Core.constructor_def) ->
            build_adt_data env ts' data_con.telescope [] (nm, fresh_var))
          con_list
      in
      let _ =
        List.map
          (fun (nmCon, tpCon) -> Env.add_to_env env nmCon (Opaque tpCon))
          (List.combine
             (List.map
                (fun (data_con : Core.constructor_def) -> data_con.cname)
                con_list)
             cs)
      in
      (Var (nm, fresh_var), adt_sig_tp)
  | Case (scrut, var, maybe_res_type, ps) -> (
      let scrut', scrut_tp' = infer_type env scrut in
      match Whnf.to_whnf scrut_tp' env.internal with
      | Neu (nm, _, tsT_args) -> (
          let tsT_args = List.rev tsT_args in
          match Env.find_opt_in_adt_env env.adt nm with
          | Some (AdtTSig (tsT, dataCNames)) ->
              if telescope_length tsT = List.length tsT_args then
                let var' =
                  match var with
                  | Some nm ->
                      let fresh_var =
                        Env.add_to_env env nm (Transparent (scrut', scrut_tp'))
                      in
                      Some (nm, fresh_var)
                  | None -> None
                in
                let branches, result_type =
                  match maybe_res_type with
                  | Some res_type -> (
                      let res_type', res_type'_tp = infer_type env res_type in
                      match res_type'_tp with
                      | Type | Kind ->
                          ( check_pattern_matching env ps scrut_tp' res_type'
                              var' tsT tsT_args dataCNames,
                            res_type' )
                      | _ ->
                          Error.create_infer_type_error pos
                            "The type of return type of Case must be either \
                             Type or Kind"
                            res_type env)
                  | None ->
                      infer_pattern_matching env ps tsT tsT_args dataCNames
                in
                let result_type =
                  match var' with
                  | Some (nm, var) ->
                      let _ = Env.rm_from_env env nm in
                      Substitution.substitute result_type
                        (Substitution.singleton_sub_map var scrut')
                  | None -> result_type
                in
                ( Case (scrut', scrut_tp', var', result_type, branches),
                  result_type )
              else
                Error.create_infer_type_error pos
                  "The number of Scrutinee's type arguments must match the ADT \
                   signature"
                  term env
          | Some (AdtDSig _) ->
              Error.create_infer_type_error pos
                "Scrutinee's type should be an ADT type and not an ADT \
                 constructor"
                term env
          | None ->
              Error.create_infer_type_error pos
                "Scrutinee's type should be an ADT type" term env)
      | _ ->
          Error.create_infer_type_error pos
            "Scrutinee's type whnf form should be a neutral term" term env)
  | IfExpr (t, b, c) -> (
      let t, tp = infer_type env t in
      match Whnf.to_whnf tp env.internal with
      | BoolType ->
          let b, b_tp = infer_type env b in
          let c, c_tp = infer_type env c in
          if Equiv.equiv b_tp c_tp env.internal then (IfExpr (t, b, c), b_tp)
          else (IfExpr (t, b, c), IfExpr (t, b_tp, c_tp))
      | _ ->
          Error.create_infer_type_error pos
            "The condition's type must be a Bool type" term env)
  | EqType (t1, t2) -> 
    let t1, tp = infer_type env t1 in
    let t2 = check_type env t2 tp in
    (EqType (t1, t2, tp), Type)
  | Refl (t1) ->
      let t1, tp = infer_type env t1 in
      (Refl (t1, tp), EqType (t1, t1, tp))
  | Subst (x, t1, t2, t3) -> (
      let t2, t2_tp = infer_type env t2 in
      match Whnf.to_whnf t2_tp env.internal with
      | EqType (a, b, t) -> (
          let fresh_var = Env.add_to_env env x (Opaque t) in
          let t1, t1_tp = infer_type env t1 in
          (* let test = Core.App(t1_tp, Core.Var (x, fresh_var)) in *)
          match Whnf.to_whnf t1_tp env.internal with
          | Type | Kind ->
              let t3 =
                check_type env t3
                  (Substitution.substitute t1
                     (Substitution.singleton_sub_map fresh_var a))
              in
              let ret_type =
                Substitution.substitute t1
                  (Substitution.singleton_sub_map fresh_var b)
              in
              let _ = Env.rm_from_env env x in
              (Subst (x, fresh_var, t, t1, t2, t3), ret_type)
          | _ ->
              Error.create_infer_type_error pos
                "The type of Subst first argument must be either Type or Kind"
                term env)
      | _ ->
          Error.create_infer_type_error pos
            "The type of Subst must be an EqType" term env)
  | FixDef (nm, dep_args, arg, arg_tp, pure_args, body_tp, body) -> (
      let dep_args =
        List.map
          (fun (nm, tp) ->
            let tp, tp_of_tp = infer_type env tp in
            match tp_of_tp with
            | Type | Kind ->
                let fresh_var = Env.add_to_env env nm (Opaque tp) in
                (nm, fresh_var, tp)
            | _ ->
                Error.create_infer_type_error pos
                  "The type of FixDef dependent arguments must be either Type \
                   or Kind"
                  term env)
          dep_args
      in
      let arg_tp, arg_tp_of_tp = infer_type env arg_tp in
      let arg_fresh_var = Env.add_to_env env arg (Opaque arg_tp) in
      let pure_args =
        List.map
          (fun (nm, tp) ->
            let tp, tp_of_tp = infer_type env tp in
            match tp_of_tp with
            | Type | Kind -> (nm, tp)
            | _ ->
                Error.create_infer_type_error pos
                  "The type of FixDef pure arguments must be either Type or \
                   Kind"
                  term env)
          pure_args
      in
      let body_tp, body_tp_of_tp = infer_type env body_tp in
      let pure_args =
        List.map
          (fun (nm, tp) -> (nm, Env.add_to_env env nm (Opaque tp), tp))
          pure_args
      in
      match (arg_tp_of_tp, body_tp_of_tp) with
      | (Type | Kind), (Type | Kind) ->
          let fix_pure_args_tp =
            List.fold_left
              (fun acc (_, _, tp) -> Core.TypeArrow (tp, acc))
              body_tp
              (List.rev ((arg, arg_fresh_var, arg_tp) :: pure_args))
          in
          let fix_tp =
            List.fold_left
              (fun (acc : Core.term) (nm, var, tp) ->
                Core.Product (nm, var, tp, acc))
              fix_pure_args_tp (List.rev dep_args)
          in
          let nm_fresh_var = Env.add_to_env env nm (Opaque fix_tp) in
          let body = check_type env body body_tp in

          let _ =
            Guard.check_totality nm_fresh_var arg_fresh_var
              (List.length dep_args) body env.internal
          in

          let _ = Env.rm_from_env env nm in
          let _ = Env.rm_from_env env arg in
          let _ =
            List.iter (fun (nm, _, _) -> Env.rm_from_env env nm) dep_args
          in
          let _ =
            List.iter (fun (nm, _, _) -> Env.rm_from_env env nm) pure_args
          in
          let nm_fresh_var' = Env.fresh_var () in
          let body =
            Substitution.substitute body
              (Substitution.singleton_sub_map nm_fresh_var
                 (Core.Var (nm, nm_fresh_var')))
          in
          let fix_pure_args_body =
            List.fold_left
              (fun (acc : Core.term) (nm, var, tp) ->
                Core.Lambda (nm, var, tp, acc))
              body
              (List.rev ((arg, arg_fresh_var, arg_tp) :: pure_args))
          in
          let fix_body =
            List.fold_left
              (fun (acc : Core.term) (nm, var, tp) ->
                Core.Lambda (nm, var, tp, acc))
              fix_pure_args_body (List.rev dep_args)
          in
          (* TODO: Refresh variable and substitute *)
          let _ =
            Env.add_to_env_with_var env nm
              (Transparent (fix_body, fix_tp))
              nm_fresh_var'
          in
          (fix_body, fix_tp)
      | _ ->
          Error.create_infer_type_error pos
            "The type of FixDef arguments must be either Type or Kind" term env)

(** [check_type env term tp] checks whether the term [term] has the expected
    type [tp] in the context of environment [env].

    @param env The environment containing variable and term bindings.
    @param term The term to check.
    @param tp The expected type of the term.
    @return The term [term] with variables resolved and type-checked.
    @raise Failure
      If type checking fails, raises an exception with an appropriate error
      message. *)
and check_type (env : Env.env) ({ pos; data = t } as term : Raw.term)
    (tp : Core.term) : Core.term =
  match t with
  | Type | Var _ | App _ | Product _ | TermWithTypeAnno _ | TypeArrow _
  | IntType | StringType | BoolType | IntLit _ | StringLit _ | BoolLit _
  | ADTSig _ | ADTDecl _ | Refl _ | EqType _ | Subst _ | FixDef _ ->
      (* For these terms, infer their type and compare to the expected type *)
      let t, t_tp = infer_type env term in
      if Equiv.equiv tp t_tp env.internal then t
      else
        Error.create_check_type_error pos
          ("Instead got:\n" ^ PrettyPrinter.term_to_string t_tp)
          term tp env
  | Lambda (x, None, body) -> (
      (* Lambda with omitted argument type *)
      match Whnf.to_whnf tp env.internal with
      | Product (_, y, y_tp, body_tp) ->
          let fresh_var = Env.add_to_env env x (Opaque y_tp) in
          (* Check the body against the expected body type with 'y' substituted by 'x' *)
          let body' =
            check_type env body
              (Substitution.substitute body_tp
                 (Substitution.singleton_sub_map y (Core.Var (x, fresh_var))))
          in
          let _ = Env.rm_from_env env x in
          Lambda (x, fresh_var, y_tp, body')
      | _ as whnf ->
          Error.create_check_type_error pos
            ("The type of Lambda must be a Product. Instead got "
            ^ PrettyPrinter.whnf_to_string whnf)
            term tp env)
  | Lambda (x, Some x_tp, body) -> (
      (* Lambda with argument type annotation 'x_tp' *)
      (* First, check the lambda without the argument type against the expected type *)
      match check_type env { pos; data = Lambda (x, None, body) } tp with
      | Lambda (_, _, arg_tp, _) as lambda ->
          (* Infer the type of the provided argument type 'x_tp' *)
          let x_tp, _ = infer_type env x_tp in
          if Equiv.equiv x_tp arg_tp env.internal then lambda
          else
            Error.create_check_type_error pos
              ("Got:\n"
              ^ PrettyPrinter.term_to_string x_tp
              ^ "\nThe expected type of lambda argument was: "
              ^ PrettyPrinter.term_to_string arg_tp)
              term tp env
      | _ ->
          Error.create_check_type_error pos "Lambda must be lambda" term tp env)
  | Kind ->
      Error.create_check_type_error pos "Kind doesn't have a type" term tp env
  | Let (x, t1, t2) ->
      (* Let-binding 'let x = t1 in t2' *)
      let t1, tp_t1 = infer_type env t1 in
      let fresh_var = Env.add_to_env env x (Transparent (t1, tp_t1)) in
      let t2 = check_type env t2 tp in
      let _ = Env.rm_from_env env x in
      Let (x, fresh_var, t1, tp_t1, t2)
  | Lemma (x, t1, t2) ->
      (* Lemma 'lemma x = t1 in t2' *)
      let t1, tp_t1 = infer_type env t1 in
      let fresh_var = Env.add_to_env env x (Opaque tp_t1) in
      let t2 = check_type env t2 tp in
      let _ = Env.rm_from_env env x in
      (* Apply the lemma by constructing 'App (Lambda (x, tp_t1, t2), t1)' *)
      App (Lambda (x, fresh_var, tp_t1, t2), t1)
  | Hole nm ->
      (* Record that the hole 'nm' has been assigned type 'tp' *)
      let _ =
        print_endline
          ("Hole " ^ nm ^ " was assigned type "
          ^ PrettyPrinter.term_to_string tp
          ^ "\nThe state of the environment at that moment:\n"
          ^ Env.env_to_string env)
      in
      Hole (nm, tp)
  (* For lemma or let definitions, check that 't' has the expected type 'tp' *)
  | LemmaDef (x, t) ->
      let t = check_type env t tp in
      let _ = Env.add_to_env env x (Opaque tp) in
      t
  | LetDef (x, t) ->
      let t = check_type env t tp in
      let _ = Env.add_to_env env x (Transparent (t, tp)) in
      t
  | Case (scrut, maybe_nm, maybe_res_type, ps) -> (
      let scrut', scrut_tp' = infer_type env scrut in
      match Whnf.to_whnf scrut_tp' env.internal with
      | Neu (nm, _, tsT_args) -> (
          let tsT_args = List.rev tsT_args in
          match Env.find_opt_in_adt_env env.adt nm with
          | Some (AdtTSig (tsT, dataCNames)) ->
              if telescope_length tsT = List.length tsT_args then
                let maybe_var =
                  match maybe_nm with
                  | Some nm ->
                      let fresh_var =
                        Env.add_to_env env nm (Transparent (scrut', scrut_tp'))
                      in
                      Some (nm, fresh_var)
                  | None -> None
                in
                let return_type =
                  match maybe_res_type with
                  | Some res_type -> (
                      let res_type', res_type'_tp = infer_type env res_type in
                      match res_type'_tp with
                      | Type | Kind ->
                          if not (Equiv.equiv res_type' tp env.internal) then
                            Error.create_check_type_error pos
                              ("Provided return type of case: "
                              ^ PrettyPrinter.term_to_string res_type'
                              ^ "doesn't match expected return type")
                              term tp env
                          else res_type'
                      | _ ->
                          Error.create_infer_type_error pos
                            "The type of provided return type of Case must be \
                             either Type or Kind"
                            res_type env)
                  | None -> tp
                in
                let branches =
                  check_pattern_matching env ps scrut_tp' return_type maybe_var
                    tsT tsT_args dataCNames
                in
                let _ =
                  match maybe_var with
                  | Some (nm, _) -> Env.rm_from_env env nm
                  | None -> ()
                in
                Case (scrut', scrut_tp', maybe_var, tp, branches)
              else
                Error.create_check_type_error pos
                  "The number of Scrutinee's type arguments must match the ADT \
                   signature"
                  term tp env
          | Some (AdtDSig _) ->
              Error.create_check_type_error pos
                "Scrutinee's type should be an ADT type and not an ADT \
                 constructor"
                term tp env
          | None ->
              Error.create_check_type_error pos
                "Scrutinee's type should be an ADT type" term tp env)
      | _ ->
          Error.create_check_type_error pos
            "Scrutinee's type whnf form should be a neutral term" term tp env)
  | IfExpr (t, b, c) -> (
      let t, t_tp = infer_type env t in
      match Whnf.to_whnf t_tp env.internal with
      | BoolType -> (
          match t with
          | Var (nm, var) ->
              let xs =
                List.map
                  (fun (branch, v) ->
                    let fresh_var =
                      Env.add_to_env env nm (Transparent (BoolLit v, BoolType))
                    in
                    let branch =
                      check_type env branch
                        (Substitution.substitute tp
                           (Substitution.singleton_sub_map var
                              (Var (nm, fresh_var))))
                    in
                    let _ = Env.rm_from_env env nm in
                    branch)
                  [ (b, true); (c, false) ]
              in
              let b, c = (List.hd xs, List.nth xs 1) in
              IfExpr (t, b, c)
          | _ ->
              let b = check_type env b tp in
              let c = check_type env c tp in
              IfExpr (t, b, c))
      | _ ->
          Error.create_infer_type_error pos
            "The condition's type must be a Bool type" term env)

and telescope_check_type_and_extend_env (env : Env.env)
    (telescope : Raw.telescope) : Core.telescope =
  match telescope with
  | Empty -> Empty
  | Cons (nm, tp, ts) ->
      let tp', _ = infer_type env tp in
      let fresh_var = Env.add_to_env env nm (Opaque tp') in
      let res =
        Core.Cons
          (nm, fresh_var, tp', telescope_check_type_and_extend_env env ts)
      in
      res

and infer_pattern_matching (env : Env.env) (ps : Raw.branch list)
    (tsT : Core.telescope) (tsT_types : Core.tp list)
    (dataCNames : Core.dataCName list) : Core.branch list * Core.tp =
  let infer_branch (env : Env.env) (tsT : Core.telescope)
      (tsT_types : Core.tp list) (tsD : Core.telescope) (args : string list)
      (term : Raw.term) :
      Core.term * Core.tp * (string * Core.Var.t * Core.tp) list =
    let tsT_vars, tsD_vars =
      extend_branch_env env tsT tsT_types tsD args term
    in
    let ts_vars = tsT_vars @ tsD_vars in
    let term, tp' = infer_type env term in
    let tp' =
      Substitution.substitute tp'
        (Substitution.of_list_sub_map
           (List.combine (List.map (fun (_, var, _) -> var) tsT_vars) tsT_types))
    in
    (* We need to remove the names from the env as the branches could over shadow each others variables but
       we need to keep the internal representation in order to check if all branches have matching types *)
    let _ = purge_branch_surface_env env ts_vars in
    (term, tp', ts_vars)
  in

  let infer_all_branches (env : Env.env) (ps : Raw.branch list)
      (tsT : Core.telescope) (tsT_types : Core.tp list) :
      (Core.branch * Core.tp) list =
    let rec loop_over_branches (env : Env.env) (ps : Raw.branch list)
        (tsT : Core.telescope) (tsT_types : Core.tp list) :
        ((Core.branch * Core.tp) * (string * Core.Var.t * Core.tp) list) list =
      match ps with
      | (pattern, term) :: ps -> (
          match pattern with
          | PatCon (raw_dataCName, args) -> (
              let dataCName = Core.dataCName_of_string raw_dataCName in
              match Env.find_opt_in_adt_env env.adt raw_dataCName with
              | Some (AdtDSig (_, tsD)) ->
                  let term, tp', ts_names_and_vars =
                    infer_branch env tsT tsT_types tsD args term
                  in
                  ( ((Core.PatCon (dataCName, ts_names_and_vars), term), tp'),
                    ts_names_and_vars )
                  :: loop_over_branches env ps tsT tsT_types
              | Some (AdtTSig _) ->
                  failwith
                    "Branch's pattern must be an ADT contructor. Found ADT \
                     type signature instead"
              | None -> failwith "Branch's pattern must be an ADT constructor")
          | PatWild ->
              let term, tp', _ = infer_branch env Empty [] Empty [] term in
              (((Core.PatWild, term), tp'), []) :: [])
      | [] -> []
    in

    let result, all_ts_vars =
      List.split (loop_over_branches env ps tsT tsT_types)
    in
    let _ = check_branch_types env (snd (List.split result)) in
    let _ = purge_all_branches_internal_env env all_ts_vars in
    result
  in
  let _ = check_exhaustivity_and_constructor_names ps dataCNames in
  let branches, tps = List.split (infer_all_branches env ps tsT tsT_types) in
  if List.is_empty tps then
    failwith "List of inferred types of branches is empty"
  else (branches, List.hd tps)

and check_pattern_matching (env : Env.env) (ps : Raw.branch list)
    (scrutinee_tp : Core.tp) (return_tp : Core.tp)
    (as_var : (string * Core.Var.t) option) (tsT : Core.telescope)
    (tsT_types : Core.tp list) (dataCNames : Core.dataCName list) :
    Core.branch list =
  let check_branch (env : Env.env) (scrutinee_tp : Core.tp)
      (return_tp : Core.tp) (as_var : (string * Core.Var.t) option)
      (raw_dataCName : string option) (tsT : Core.telescope)
      (tsT_types : Core.tp list) (tsD : Core.telescope) (args : string list)
      ({ pos; _ } as term : Raw.term) :
      Core.term * (string * Core.Var.t * Core.tp) list =
    let res = extend_branch_env env tsT tsT_types tsD args term in
    let ts_vars = fst res @ snd res in
    match raw_dataCName with
    | Some raw_dataCName ->
        let data_con =
          match Env.find_opt_in_env env raw_dataCName with
          | Some (var, env_var) -> (
              match env_var with
              | Opaque _ -> Core.Var (raw_dataCName, var)
              | Transparent _ ->
                  Error.create_infer_type_error pos
                    ("Constructor is transparent: " ^ raw_dataCName)
                    term env)
          | None ->
              Error.create_infer_type_error pos
                ("Couldn't find constructor in env: " ^ raw_dataCName)
                term env
        in
        let data_con =
          List.fold_left
            (fun acc (nm, var, _) -> Core.App (acc, Core.Var (nm, var)))
            data_con ts_vars
        in
        let term =
          match as_var with
          | Some (nm, var) ->
              let fresh_var =
                Env.add_to_env env nm (Transparent (data_con, scrutinee_tp))
              in
              let term =
                check_type env term
                  (Substitution.substitute return_tp
                     (Substitution.singleton_sub_map var
                        (Core.Var (nm, fresh_var))))
              in
              let _ = Env.rm_from_env env nm in
              term
          | None -> check_type env term return_tp
        in
        (term, ts_vars)
    (* Wild card case *)
    (* TODO: Wildcard may need to be adjusted for dependent types *)
    | None -> (check_type env term return_tp, ts_vars)
  in
  let check_all_branches (env : Env.env) (ps : Raw.branch list)
      (scrutinee_tp : Core.tp) (return_tp : Core.tp)
      (as_var : (string * Core.Var.t) option) (tsT : Core.telescope)
      (tsT_types : Core.tp list) : Core.branch list =
    let rec loop_over_branches (env : Env.env) (ps : Raw.branch list) :
        Core.branch list =
      match ps with
      | (pattern, term) :: ps -> (
          match pattern with
          | PatCon (raw_dataCName, args) -> (
              let dataCName = Core.dataCName_of_string raw_dataCName in
              match Env.find_opt_in_adt_env env.adt raw_dataCName with
              | Some (AdtDSig (_, tsD)) ->
                  let term, ts_names_and_vars =
                    check_branch env scrutinee_tp return_tp as_var
                      (Some raw_dataCName) tsT tsT_types tsD args term
                  in
                  let _ = purge_branch_env env ts_names_and_vars in
                  (Core.PatCon (dataCName, ts_names_and_vars), term)
                  :: loop_over_branches env ps
              | Some (AdtTSig _) ->
                  failwith
                    "Branch's pattern must be an ADT contructor. Found ADT \
                     type signature instead"
              | None -> failwith "Branch's pattern must be an ADT constructor")
          | PatWild ->
              let term, _ =
                check_branch env scrutinee_tp return_tp as_var None Empty []
                  Empty [] term
              in
              (Core.PatWild, term) :: [])
      | [] -> []
    in
    loop_over_branches env ps
  in
  let _ = check_exhaustivity_and_constructor_names ps dataCNames in
  check_all_branches env ps scrutinee_tp return_tp as_var tsT tsT_types

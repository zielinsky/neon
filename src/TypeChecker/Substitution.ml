module VarMap = Map.Make (Core.Var)

type sub_map = Core.term VarMap.t

let add_to_sub_map (var : Core.Var.t) (t : Core.term) (sub_map : sub_map) :
    sub_map =
  VarMap.add var t sub_map

let singleton_sub_map (var : Core.Var.t) (t : Core.term) : sub_map =
  VarMap.singleton var t

let find_opt_sub_map (var : Core.Var.t) (sub_map : sub_map) : Core.term option =
  VarMap.find_opt var sub_map

let of_list_sub_map (xs : (Core.Var.t * Core.term) list) : sub_map =
  VarMap.of_list xs

let merge_sub_maps (sub1 : sub_map) (sub2 : sub_map) : sub_map =
  VarMap.fold VarMap.add sub1 sub2

let empty_sub_map : sub_map = VarMap.empty

(** [substitute t sub] performs capture-avoiding substitution on term [t] using
    the substitution map [sub]. It replaces variables in [t] according to [sub],
    ensuring that bound variables are correctly handled to prevent variable
    capture.

    @param t The term in which to perform substitution.
    @param sub The substitution map, mapping variable identifiers to terms.
    @return A new term where variables have been substituted according to [sub].
*)
let rec substitute (t : Core.term) (sub : sub_map) : Core.term =
  match t with
  | Var (nm, x) -> (
      match find_opt_sub_map x sub with Some t -> t | None -> Var (nm, x))
  | Lambda (nm, x, tp, body) ->
      let y = Env.fresh_var () in
      Lambda
        ( nm,
          y,
          substitute tp sub,
          substitute body (add_to_sub_map x (Core.Var (nm, y)) sub) )
  | Product (nm, x, tp, body) ->
      let y = Env.fresh_var () in
      Product
        ( nm,
          y,
          substitute tp sub,
          substitute body (add_to_sub_map x (Core.Var (nm, y)) sub) )
  | App (t1, t2) -> App (substitute t1 sub, substitute t2 sub)
  | TypeArrow (t1, t2) -> TypeArrow (substitute t1 sub, substitute t2 sub)
  | Let (nm, x, t, tp_t, body) ->
      let y = Env.fresh_var () in
      Let
        ( nm,
          y,
          substitute t sub,
          substitute tp_t sub,
          substitute body (add_to_sub_map x (Core.Var (nm, y)) sub) )
  | Type | Kind | Hole _ | IntType | StringType | BoolType | IntLit _
  | StringLit _ | BoolLit _ ->
      t
  | Case (scrutinee, scrutinee_tp, var, tp, branches) ->
      let scrutinee' = substitute scrutinee sub in
      let scrutinee_tp' = substitute scrutinee_tp sub in
      let var_sub, var' =
        match var with
        | Some (nm, var) ->
            let fresh_var = Env.fresh_var () in
            ( singleton_sub_map var (Core.Var (nm, fresh_var)),
              Some (nm, fresh_var) )
        | None -> (empty_sub_map, None)
      in
      let tp' = substitute tp (merge_sub_maps sub var_sub) in
      let branches' =
        List.map
          (fun (pattern, t) ->
            match pattern with
            | Core.PatWild ->
                (Core.PatWild, substitute t (merge_sub_maps sub var_sub))
            | Core.PatCon (con_nm, vars) ->
                let sub, rev_vars =
                  List.fold_left
                    (fun (sub_map, new_vars) (nm, var, tp) ->
                      let fresh_var = Env.fresh_var () in
                      ( add_to_sub_map var (Core.Var (nm, fresh_var)) sub_map,
                        (nm, fresh_var, tp) :: new_vars ))
                    (sub, []) vars
                in
                ( Core.PatCon (con_nm, List.rev rev_vars),
                  substitute t (merge_sub_maps sub var_sub) ))
          branches
      in
      Case (scrutinee', scrutinee_tp', var', tp', branches')
  | IfExpr (t, b1, b2) ->
      IfExpr (substitute t sub, substitute b1 sub, substitute b2 sub)
  | EqType (t1, t2, tp) ->
      EqType (substitute t1 sub, substitute t2 sub, substitute tp sub)
  | Refl (t, tp) -> Refl (substitute t sub, substitute tp sub)
  | Subst (nm, var, tp, t1, t2, t3) ->
      let y = Env.fresh_var () in
      Subst
        ( nm,
          y,
          substitute tp (add_to_sub_map var (Core.Var (nm, y)) sub),
          substitute t1 (add_to_sub_map var (Core.Var (nm, y)) sub),
          substitute t2 (add_to_sub_map var (Core.Var (nm, y)) sub),
          substitute t3 (add_to_sub_map var (Core.Var (nm, y)) sub) )
  | FixDef (nm, nm_var, args, arg, arg_var, arg_tp, body_tp, body) ->
      let y = Env.fresh_var () in
      let sub = add_to_sub_map nm_var (Core.Var (nm, y)) sub in

      let sub, args_rev =
        List.fold_left
          (fun (sub_map', args') (var_nm, var, var_tp) ->
            let var_tp = substitute var_tp sub in
            let fresh_var = Env.fresh_var () in
            ( add_to_sub_map var (Core.Var (var_nm, fresh_var)) sub_map',
              (var_nm, fresh_var, var_tp) :: args' ))
          (sub, []) args
      in
      let args = List.rev args_rev in
      let arg_tp = substitute arg_tp sub in

      let arg_var' = Env.fresh_var () in
      let sub = add_to_sub_map arg_var (Core.Var (nm, arg_var')) sub in

      FixDef
        ( nm,
          y,
          args,
          arg,
          arg_var',
          substitute arg_tp sub,
          substitute body_tp sub,
          substitute body sub )

(** [substitute_whnf t sub] performs substitution on a term in weak head normal
    form (WHNF) [t] using the substitution map [sub].

    @param t The WHNF term in which to perform substitution.
    @param sub The substitution map.
    @return A new WHNF term with substitutions applied. *)

let rec substitute_in_telescope (ts : Core.telescope) (sub : sub_map) :
    Core.telescope =
  match ts with
  | Cons (nm, var, tp, tl) ->
      Cons (nm, var, substitute tp sub, substitute_in_telescope tl sub)
  | Empty -> Empty

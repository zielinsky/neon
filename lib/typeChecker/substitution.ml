module VarMap = Map.Make (Ast.Var)

type sub_map = Ast.term VarMap.t

let add_to_sub_map (var : Ast.Var.t) (t : Ast.term) (sub_map : sub_map) :
    sub_map =
  VarMap.add var t sub_map

let singleton_sub_map (var : Ast.Var.t) (t : Ast.term) : sub_map =
  VarMap.singleton var t

let find_opt_sub_map (var : Ast.Var.t) (sub_map : sub_map) : Ast.term option =
  VarMap.find_opt var sub_map

let of_list_sub_map (xs : (Ast.Var.t * Ast.term) list) : sub_map =
  VarMap.of_list xs

let empty_sub_map : sub_map = VarMap.empty

(** [substitute t sub] performs capture-avoiding substitution on term [t] using
    the substitution map [sub]. It replaces variables in [t] according to [sub],
    ensuring that bound variables are correctly handled to prevent variable
    capture.

    @param t The term in which to perform substitution.
    @param sub The substitution map, mapping variable identifiers to terms.
    @return A new term where variables have been substituted according to [sub].
*)
let rec substitute (t : Ast.term) (sub : sub_map) : Ast.term =
  match t with
  | Var (nm, x) -> (
      match find_opt_sub_map x sub with Some t -> t | None -> Var (nm, x))
  | Lambda (nm, x, tp, body) ->
      let y = Env.fresh_var () in
      Lambda
        ( nm,
          y,
          substitute tp sub,
          substitute body (add_to_sub_map x (Ast.Var (nm, y)) sub) )
  | Product (nm, x, tp, body) ->
      let y = Env.fresh_var () in
      Product
        ( nm,
          y,
          substitute tp sub,
          substitute body (add_to_sub_map x (Ast.Var (nm, y)) sub) )
  | App (t1, t2) -> App (substitute t1 sub, substitute t2 sub)
  | TypeArrow (t1, t2) -> TypeArrow (substitute t1 sub, substitute t2 sub)
  | Let (nm, x, t, tp_t, body) ->
      let y = Env.fresh_var () in
      Let
        ( nm,
          y,
          substitute t sub,
          substitute tp_t sub,
          substitute body (add_to_sub_map x (Ast.Var (nm, y)) sub) )
  | Type | Kind | Hole _ | IntType | StringType | BoolType | IntLit _
  | StringLit _ | BoolLit _ ->
      t
  | Case (scrutinee, matchPats) ->
      let scrutinee' = substitute scrutinee sub in
      let matchPats' =
        List.map
          (fun (pattern, t) ->
            match pattern with
            | Ast.PatWild -> (Ast.PatWild, substitute t sub)
            | Ast.PatCon (con_nm, vars) ->
                let sub, rev_vars =
                  List.fold_left
                    (fun (sub_map, new_vars) (nm, var) ->
                      let fresh_var = Env.fresh_var () in
                      ( add_to_sub_map var (Ast.Var (nm, fresh_var)) sub_map,
                        (nm, fresh_var) :: new_vars ))
                    (sub, []) vars
                in
                (Ast.PatCon (con_nm, List.rev rev_vars), substitute t sub))
          matchPats
      in
      Case (scrutinee', matchPats')

(** [substitute_whnf t sub] performs substitution on a term in weak head normal
    form (WHNF) [t] using the substitution map [sub].

    @param t The WHNF term in which to perform substitution.
    @param sub The substitution map.
    @return A new WHNF term with substitutions applied. *)
let substitute_whnf (t : Ast.whnf) (sub : sub_map) : Ast.whnf =
  match t with
  | Type | Kind | IntType | StringType | BoolType | IntLit _ | StringLit _
  | BoolLit _ | Case _ ->
      t
  | Neu (nm, var, term_list) ->
      Neu (nm, var, List.map (fun t -> substitute t sub) term_list)
  | Neu_with_Hole (nm, tp, term_list) ->
      Neu_with_Hole (nm, tp, List.map (fun t -> substitute t sub) term_list)
  | Lambda (nm, var, tp, body) ->
      Lambda (nm, var, substitute tp sub, substitute body sub)
  | Product (nm, var, tp, body) ->
      Product (nm, var, substitute tp sub, substitute body sub)

let rec substitute_in_telescope (ts : Ast.telescope) (sub : sub_map) :
    Ast.telescope =
  match ts with
  | Cons (nm, var, tp, tl) ->
      Cons (nm, var, substitute tp sub, substitute_in_telescope tl sub)
  | Empty -> Empty

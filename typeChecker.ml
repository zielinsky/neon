(* modules *)
open UExpr
module EnvHashtbl = Hashtbl.Make(String)

(* types *)
type var = int
type counter = int ref

type term = 
  | Type
  | Kind
  | Var of var
  | Lambda of string * var * term * term
  | Product of string * var * term * term
  | App of term * term

type env = ((var * term) EnvHashtbl.t * counter)

type whnf = 
  | Type
  | Kind
  | Neu of var * term list
  | Lambda of var * term * term
  | Product of var * term * term

let rec to_whnf (t: term) : whnf = 
  begin match t with
  | Type -> Type
  | Kind -> Kind
  | Var x -> Neu (x, [])
  | Lambda (x_name, x, x_tp, body) -> Lambda (x, x_tp, body)
  | Product (x_name, x, x_tp, body) -> Product (x, x_tp, body)
  | App (t1, t2) ->
    begin match to_whnf t1 with
    | _ -> failwith "not implemented"
    end
  | _ -> failwith "not implemented"
  end

let rec substitute (t: term) (x: var) (s: term) : term =
  failwith "not implemented"

let rec equiv (env: env) (t1 : term) (t2 : term) : bool =
  failwith "not implemented"

(* functions *)

let rec infer_type (env : env) (t: UExpr.term) : (term * term) = 
  let (var_HT, var_cnt) = env in
  match t with 
  | Type -> (Type, Kind)
  | Kind -> raise (Failure "Can't infer the type of Kind")
  | Var x -> 
    begin match EnvHashtbl.find_opt var_HT x with
    | Some (y, tp) -> (Var y, tp) 
    | None -> raise (Failure ("Variable " ^ x ^ " not found"))
    end
  | Lambda (_, None, _) -> raise (Failure "Can't infer the type of lambda with omitted argument type")
  | Lambda (x, Some tp, t) -> 
    let (tp, tp_of_tp) = infer_type env tp in
    begin match tp_of_tp with
      | Type | Kind -> 
        let fresh_var = !var_cnt in
        let _ = EnvHashtbl.add var_HT x (fresh_var, tp) in
        let _ = var_cnt := !var_cnt + 1 in
        let (body, body_tp) = infer_type env t in
        let _ = EnvHashtbl.remove var_HT x in
        (Lambda (x, fresh_var, tp, body) , Product (x, fresh_var, tp, body_tp))
      | _ -> failwith "The type of Lambda argument type must be either Type or Kind"
    end
  | Product (x, tp, t) ->
    let (tp, tp_of_tp) = infer_type env tp in
    begin match tp_of_tp with
      | Type | Kind -> 
        let fresh_var = !var_cnt in
        let _ = EnvHashtbl.add var_HT x (fresh_var, tp) in
        let _ = var_cnt := !var_cnt + 1 in
        let (body, body_tp) = infer_type env t in
        let _ = EnvHashtbl.remove var_HT x in
        begin match body_tp with
        | Type | Kind -> 
          (Product (x, fresh_var, tp, body) , body_tp)
        | _ -> failwith "The type of Product body type must be either Type or Kind"
        end
      | _ -> failwith "The type of Product argument type must be either Type or Kind"
    end
  | App (t1, t2) ->
    let (t1, t1_tp) = infer_type env t1 in
    begin match to_whnf t1_tp with
    | Product (x, x_tp, body) ->
      let t2 = check_type env t2 x_tp in
      (App (t1, t2), substitute body x t2)
    | _ -> failwith "The type of Application's first argument must be a Product"
    end
and check_type (env : env) (t: UExpr.term) (tp: term) : term =
  let (var_HT, var_cnt) = env in
  match t with 
  | Type | Var _ | App _ | Product _ -> 
    let (t, t_tp) = infer_type env t in
    if equiv env tp t_tp then t else failwith "Type mismatch"
  | Lambda (x, None, body) -> 
    begin match to_whnf tp with
    | Product (y, y_tp, body_tp) -> 
      let fresh_var = !var_cnt in
      let _ = EnvHashtbl.add var_HT x (fresh_var, y_tp) in
      let _ = var_cnt := !var_cnt + 1 in
      let body' = check_type env body (substitute (Var fresh_var) y body_tp) in 
      Lambda (x, fresh_var, y_tp, body')
    | _ -> failwith "The type of Lambda must be a Product"
    end
  | Lambda (x, Some x_tp, body) ->
    begin match (check_type env (Lambda (x, None, body)) tp) with
    | Lambda (_, _, arg_tp, _) as lambda -> 
      let (x_tp, _) = infer_type env x_tp in
      if equiv env x_tp arg_tp then lambda else failwith "Type mismatch"
    | _ -> failwith "Lambda must be lambda lolz"
    end
  | Kind -> failwith "Kind doesn't have a type"

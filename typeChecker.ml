(* modules *)
open UExpr

type var = int

module Var : sig type t = var val compare : 'a -> 'a -> int end = struct
  type t = var
  let compare = compare
end

module EnvHashtbl = Hashtbl.Make(String)
module VarMap = Map.Make(Var)

(* types *)
type counter = int ref

type term = 
  | Type
  | Kind
  | Var of var
  | Lambda of string * var * term * term
  | Product of string * var * term * term
  | App of term * term

type env_var = 
  | Abstract of term
  | Transparent of term * term

type env = (var * env_var) EnvHashtbl.t 
let counter = ref 0

type sub_map = term VarMap.t

(* The term list in Neu constructor is kept in reverse order *)

type whnf = 
  | Type
  | Kind
  | Neu of var * term list
  | Lambda of var * term * term
  | Product of var * term * term

let fresh_var () : int =
  let fresh_var = !counter in
  let _ = counter := !counter + 1 in
  fresh_var

let rec substitute (t: term) (sub: sub_map) : term =
  begin match t with
  | Var x -> begin match VarMap.find_opt x sub with
    | Some t -> t
    | None -> Var x
    end
  | Lambda (nm, x, x_tp, body) -> 
    let y = fresh_var () in
    Lambda (nm, y, (substitute t sub), substitute body (VarMap.add x (Var y) sub))
  | Product (nm, x, x_tp, body) ->
    let y = fresh_var () in
    Product (nm, y, (substitute t sub), substitute body (VarMap.add x (Var y) sub))
  | App (t1, t2) -> App (substitute t1 sub, substitute t2 sub)
  (* TODO: ASK PPO *)
  | Type | Kind -> t
  end
  
  
let rec to_whnf (t: term) : whnf = 
  begin match t with
  | Type -> Type
  | Kind -> Kind
  | Var x -> Neu (x, [])
  | Lambda (x_name, x, x_tp, body) -> Lambda (x, x_tp, body)
  | Product (x_name, x, x_tp, body) -> Product (x, x_tp, body)
  | App (t1, t2) ->
    begin match to_whnf t1 with
    | Neu (x, ts) -> Neu (x, (t1 :: ts))
    | Lambda (x, x_tp, body) -> to_whnf (substitute body (VarMap.singleton x t2))
    | _ -> failwith "Expected Neu or Lambda when reducing Application with whnf"
    end
  end


let rec equiv (t1: term) (t2: term) : bool =
  match (to_whnf t1, to_whnf t2) with
  | (Type, Type) -> true
  | (Kind, Kind) -> true
  | (Neu (x1, ts1), Neu (x2, ts2)) -> 
    if x1 = x2 then 
      List.for_all2 equiv ts1 ts2
    else false
  | (Lambda (x1, x1_tp, body1), Lambda (x2, x2_tp, body2)) ->
    if equiv x1_tp x2_tp then
      let fresh_var = fresh_var () in
      let body1' = substitute body1 (VarMap.singleton x1 (Var fresh_var)) in
      let body2' = substitute body2 (VarMap.singleton x2 (Var fresh_var)) in
      equiv body1' body2'
    else
      false
  (* TODO: ASK PPO *)
  | (Product _, Product _) -> failwith "Can't compare two Products?"
  | _ -> false

(* functions *)

let rec infer_type (env: env) (t: UExpr.term) : (term * term) = 
  match t with 
  | Type -> (Type, Kind)
  | Kind -> raise (Failure "Can't infer the type of Kind")
  | Var x -> 
    begin match EnvHashtbl.find_opt env x with
    | Some (y, Abstract tp) -> (Var y, tp) 
    (* TODO: ASK PPO *)
    | Some (y, Transparent (body, tp)) -> (body, tp) 
    | None -> raise (Failure ("Variable " ^ x ^ " not found"))
    end
  | Lambda (_, None, _) -> raise (Failure "Can't infer the type of lambda with omitted argument type")
  | Lambda (x, Some tp, t) -> 
    let (tp, tp_of_tp) = infer_type env tp in
    begin match tp_of_tp with
      | Type | Kind -> 
        let fresh_var = fresh_var () in
        let _ = EnvHashtbl.add env x (fresh_var, Abstract tp) in
        let (body, body_tp) = infer_type env t in
        let _ = EnvHashtbl.remove env x in
        (Lambda (x, fresh_var, tp, body) , Product (x, fresh_var, tp, body_tp))
      | _ -> failwith "The type of Lambda argument type must be either Type or Kind"
    end
  | Product (x, tp, t) ->
    let (tp, tp_of_tp) = infer_type env tp in
    begin match tp_of_tp with
      | Type | Kind -> 
        let fresh_var = fresh_var () in
        let _ = EnvHashtbl.add env x (fresh_var, Abstract tp) in
        let (body, body_tp) = infer_type env t in
        let _ = EnvHashtbl.remove env x in
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
    | Product (x, x_tp, tp_body) ->
      let t2 = check_type env t2 x_tp in
      (App (t1, t2), substitute tp_body (VarMap.singleton x t2))
    | _ -> failwith "The type of Application's first argument must be a Product"
    end
  | TermWithTypeAnno (t, tp) -> 
    let (tp, tp_of_tp) = infer_type env tp in 
    begin match tp_of_tp with
    | Type | Kind -> (check_type env t tp, tp)
    | _ -> failwith "Type annotation must be a Type or Kind"
    end
  | Let (x, t1, t2) -> 
    let (t1, tp_t1) = infer_type env t1 in
    let fresh_var = fresh_var () in
    let _ = EnvHashtbl.add env x (fresh_var, Transparent (t1, tp_t1)) in
    infer_type env t2
  | Lemma (x, t1, t2) -> 
    let (t1, tp_t1) = infer_type env t1 in
    let fresh_var = fresh_var () in
    let _ = EnvHashtbl.add env x (fresh_var, Abstract tp_t1) in
    infer_type env t2
    
and check_type (env : env) (t: UExpr.term) (tp: term) : term =
  match t with 
  | Type | Var _ | App _ | Product _ | TermWithTypeAnno _ | Let _ | Lemma _-> 
    let (t, t_tp) = infer_type env t in
    if equiv tp t_tp then t else failwith "Type mismatch"
  | Lambda (x, None, body) -> 
    begin match to_whnf tp with
    | Product (y, y_tp, body_tp) -> 
      let fresh_var = fresh_var () in
      let _ = EnvHashtbl.add env x (fresh_var, Abstract y_tp) in
      let body' = check_type env body (substitute (Var fresh_var) (VarMap.singleton y body_tp)) in 
      Lambda (x, fresh_var, y_tp, body')
    | _ -> failwith "The type of Lambda must be a Product"
    end
  | Lambda (x, Some x_tp, body) ->
    begin match (check_type env (Lambda (x, None, body)) tp) with
    | Lambda (_, _, arg_tp, _) as lambda -> 
      let (x_tp, _) = infer_type env x_tp in
      if equiv x_tp arg_tp then lambda else failwith "Type mismatch"
    | _ -> failwith "Lambda must be lambda lolz"
    end
  | Kind -> failwith "Kind doesn't have a type"
  
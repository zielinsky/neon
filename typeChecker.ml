(* modules *)
open UExpr
module EnvHashtbl = Hashtbl.Make(String)

(* types *)
type var = int

type term = 
  | Prop
  | Type
  | Var of var
  | Lambda of string * var * term * term
  | Product of string * var * term * term
  | App of term * term

type env = ((var * term) EnvHashtbl.t * int)

let rec infer_type (env : env) (t: UExpr.term) : (term * term option) = 
  let (var_HT, var_cnt) = env in
  match t with 
  | Prop -> (Prop, Some Type)
  | Type -> (Type, None)
  | Var x -> 
    begin match EnvHashtbl.find_opt var_HT x with
    | Some (y, tp) -> (Var y, Some tp)
    | None -> raise (Failure ("Variable " ^ x ^ " not found"))
    end
  | Lambda (_, None, _) -> raise (Failure "Can't infer the type of omitted argument")
  | Lambda (x, Some tp, t) -> 
    let (arg_tp, _) = infer_type env tp in
    let _ = EnvHashtbl.add var_HT x (var_cnt, arg_tp) in
    let var_cnt = var_cnt + 1 in
    let env = (var_HT, var_cnt) in
    let (body, body_tp) = infer_type env t in
    let _ = EnvHashtbl.remove var_HT x in
    begin match body_tp with
    | Some body_tp -> 
        (Lambda (x, var_cnt, arg_tp, body_tp), Some (Product (x, var_cnt, arg_tp, body_tp)))
    | None -> raise (Failure "Can't infer the type of lambda expression")
    end
  | _ -> raise (Failure "Not implemented")

open Ast

type var = int

module Var : sig type t = var val compare : 'a -> 'a -> int end = struct
  type t = var
  let compare = compare
end

module EnvHashtbl = Hashtbl.Make(String)
module VarMap = Map.Make(Var)

type term = 
  | Type
  | Kind
  | Var of string * var
  | Lambda of string * var * tp * term
  | Product of string * var * tp * tp
  | App of term * term
and tp = term
  (* | Hole of string * tp  *)

type env_var = 
(* Abstract -> Opaque *)
  | Abstract of tp
  | Transparent of term * tp

type env = (var * env_var) EnvHashtbl.t 
let counter = ref 0

type sub_map = term VarMap.t

(* The term list in Neu constructor is kept in reverse order *)

type whnf = 
  | Type
  | Kind
  | Neu of var * term list
  (* | Neu_with_Hole of string * tp * term list *)
  | Lambda of var * tp * term
  | Product of var * tp * tp

let create_env () : env =
  EnvHashtbl.create 10

let create_error_msg (pos : Ast.position) (msg: string) : string =
  "Error at " ^ (Int.to_string pos.start.pos_lnum) ^ ":" ^ (Int.to_string pos.start.pos_cnum) ^ "\n" ^ msg

let fresh_var () : int =
  let fresh_var = !counter in
  let _ = counter := !counter + 1 in
  fresh_var

let rec substitute (t: term) (sub: sub_map) : term =
  begin match t with
  | Var (nm, x) -> begin match VarMap.find_opt x sub with
    | Some t -> t
    | None -> Var (nm, x)
    end
  | Lambda (nm, x, _, body) -> 
    let y = fresh_var () in
    Lambda (nm, y, (substitute t sub), substitute body (VarMap.add x (Var ("", y)) sub))
  | Product (nm, x, _, body) ->
    let y = fresh_var () in
    Product (nm, y, (substitute t sub), substitute body (VarMap.add x (Var ("", y)) sub))
  | App (t1, t2) -> App (substitute t1 sub, substitute t2 sub)
  | Type | Kind -> t
  (* | Hole -> t*)
  end
  
  
let rec to_whnf (t: term) : whnf = 
  begin match t with
  | Type -> Type
  | Kind -> Kind
  (* For Opaque Neu, for transparent add var to env and recurse on body*)
  | Var (_, x) -> Neu (x, [])
  | Lambda (_, x, x_tp, body) -> Lambda (x, x_tp, body)
  | Product (_, x, x_tp, body) -> Product (x, x_tp, body)
  | App (t1, t2) ->
    begin match to_whnf t1 with
    | Neu (x, ts) -> Neu (x, (t1 :: ts))
    | Lambda (x, _, body) -> to_whnf (substitute body (VarMap.singleton x t2))
    | _ -> failwith "Expected Neu or Lambda when reducing Application with whnf"
    end
   (* For let add (let x = A in B) add A to env and recurse on B, substitute x in type of B*) 
   (* Hole like Neu *)
  end


let rec equiv (t1: term) (t2: term) : bool =
  match (to_whnf t1, to_whnf t2) with
  | (Type, Type) -> true
  | (Kind, Kind) -> true
  | (Neu (x1, ts1), Neu (x2, ts2)) -> 
    x1 = x2 
    && List.length ts1 = List.length ts2 
    && List.for_all2 equiv ts1 ts2
  | (Lambda (x1, x1_tp, body1), Lambda (x2, x2_tp, body2)) ->
    if equiv x1_tp x2_tp then
      let fresh_var = fresh_var () in
      let body1' = substitute body1 (VarMap.singleton x1 (Var ("", fresh_var))) in
      let body2' = substitute body2 (VarMap.singleton x2 (Var ("", fresh_var))) in
      equiv body1' body2'
    else
      false
  (* TODO *)
  | (Product _, Product _) -> failwith "not implemented"
  | _ -> false
  (* When comparing two Holes check like Neu terms *)
  (* When comparing Hole with other non matching term tell user what the hole should be equal to *)

(* functions *)

let rec infer_type (env: env) ({pos; data = t}: Ast.term) : (term * term) = 
  match t with 
  | Type -> (Type, Kind)
  | Kind -> failwith (create_error_msg pos "Can't infer the type of Kind")
  | Var x -> 
    begin match EnvHashtbl.find_opt env x with
    | Some (y, (Abstract tp | (Transparent (_, tp)))) -> (Var (x, y), tp) 
    | None -> failwith (create_error_msg pos ("Variable " ^ x ^ " not found"))
    end
  | Lambda (_, None, _) -> failwith (create_error_msg pos "Can't infer the type of lambda with omitted argument type")
  | Lambda (x, Some tp, t) -> 
    let (tp, tp_of_tp) = infer_type env tp in
    begin match tp_of_tp with
      | Type | Kind -> 
        let fresh_var = fresh_var () in
        let _ = EnvHashtbl.add env x (fresh_var, Abstract tp) in
        let (body, body_tp) = infer_type env t in
        let _ = EnvHashtbl.remove env x in
        (Lambda (x, fresh_var, tp, body) , Product (x, fresh_var, tp, body_tp))
      | _ -> failwith (create_error_msg pos "The type of Lambda argument type must be either Type or Kind")
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
        | _ -> failwith (create_error_msg pos "The type of Product body type must be either Type or Kind")
        end
      | _ -> failwith (create_error_msg pos "The type of Product argument type must be either Type or Kind")
    end
  | App (t1, t2) ->
    let (t1, t1_tp) = infer_type env t1 in
    begin match to_whnf t1_tp with
    | Product (x, x_tp, tp_body) ->
      let t2 = check_type env t2 x_tp in
      (App (t1, t2), substitute tp_body (VarMap.singleton x t2))
    | _ -> failwith (create_error_msg pos "The type of Application's first argument must be a Product")
    end
  | TermWithTypeAnno (t, tp) -> 
    let (tp, tp_of_tp) = infer_type env tp in 
    begin match tp_of_tp with
    | Type | Kind -> (check_type env t tp, tp)
    | _ -> failwith (create_error_msg pos "Type annotation must be a Type or Kind")
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
    let (t2, tp_t2) = infer_type env t2 in
    let _ = EnvHashtbl.remove env x in
    (App (Lambda (x, fresh_var, tp_t1, t2), t1), (substitute tp_t2 (VarMap.singleton fresh_var t1)))

    
and check_type (env : env) ({pos; data = t} as term: Ast.term) (tp: term) : term =
  match t with 
  (* Add check type for let and lemma (we know the type of t2)*)
  | Type | Var _ | App _ | Product _ | TermWithTypeAnno _ | Let _ | Lemma _-> 
    let (t, t_tp) = infer_type env term in
    if equiv tp t_tp then t else failwith (create_error_msg pos (create_error_msg pos "Type mismatch"))
  | Lambda (x, None, body) -> 
    begin match to_whnf tp with
    | Product (y, y_tp, body_tp) -> 
      let fresh_var = fresh_var () in
      let _ = EnvHashtbl.add env x (fresh_var, Abstract y_tp) in
      let body' = check_type env body (substitute (Var ("", fresh_var)) (VarMap.singleton y body_tp)) in 
      Lambda (x, fresh_var, y_tp, body')
    | _ -> failwith (create_error_msg pos "The type of Lambda must be a Product")
    end
  | Lambda (x, Some x_tp, body) ->
    begin match (check_type env {pos = pos; data = (Lambda (x, None, body))} tp) with
    | Lambda (_, _, arg_tp, _) as lambda -> 
      let (x_tp, _) = infer_type env x_tp in
      if equiv x_tp arg_tp then lambda else failwith "Type mismatch"
    | _ -> failwith (create_error_msg pos "Lambda must be lambda lolz")
    end
  | Kind -> failwith (create_error_msg pos "Kind doesn't have a type")
  
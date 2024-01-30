open Ast
open PrettyPrinter

module VarMap = Map.Make(Int)
type sub_map = term VarMap.t


(* The term list in Neu constructor is kept in reverse order *)
type whnf = 
  | Type
  | Kind
  | Neu of var * term list
  | Neu_with_Hole of string * tp * term list
  | Lambda of var * tp * term
  | Product of var * tp * tp

let create_error_msg (pos : ParserAst.position) (msg: string) : string =
  "Error at " ^ (Int.to_string pos.start.pos_lnum) ^ ":" ^ (Int.to_string pos.start.pos_cnum) ^ "\n" ^ msg

let rec substitute (t: term) (sub: sub_map) : term =
  begin match t with
  | Var (nm, x) -> begin match VarMap.find_opt x sub with
    | Some t -> t
    | None -> Var (nm, x)
    end
  | Lambda (nm, x, tp, body) ->
    let y = fresh_var () in
    Lambda (nm, y, (substitute tp sub), substitute body (VarMap.add x (Var (nm, y)) sub))
  | Product (nm, x, tp, body) ->
    let y = fresh_var () in
    Product (nm, y, (substitute tp sub), substitute body (VarMap.add x (Var (nm, y)) sub))
  | App (t1, t2) -> App (substitute t1 sub, substitute t2 sub)
  | TypeArrow (t1, t2) -> TypeArrow (substitute t1 sub, substitute t2 sub)
  | Let (nm, x, t, tp_t, body) -> 
    let y = fresh_var () in
    Let (nm, y, (substitute t sub), (substitute tp_t sub), substitute body (VarMap.add x (Var (nm, y)) sub))
  | Type | Kind | Triangle | Hole _ -> t
  end

let substitute_whnf (t: whnf) (sub: sub_map) : whnf = 
  begin match t with
  | Type | Kind -> t
  | Neu (var, term_list) -> Neu(var, List.map (fun t -> substitute t sub) term_list)
  | Neu_with_Hole (nm, tp, term_list) -> Neu_with_Hole(nm, tp, List.map (fun t -> substitute t sub) term_list)
  | Lambda (var, tp, body) -> Lambda (var, (substitute tp sub), (substitute body sub))
  | Product (var, tp, body) -> Product (var, (substitute tp sub), (substitute body sub))
  end
  
let rec to_whnf (t: term) (env: termEnv) : whnf = 
  begin match t with
  | Type -> Type
  | Kind -> Kind
  | Triangle -> failwith ("Triangle shouldn't be reduced to whnf")
  (* For Opaque Neu, for transparent add var to env and recurse on body ??? *)
  (* Ask PPO 26/01*)
  | Var (nm, x) -> 
    begin match find_opt_in_termEnv env x with
    | Some (Opaque _) -> Neu(x, [])
    | Some (Transparent (body, _)) -> to_whnf body env
    | None -> failwith ("Variable " ^ nm ^ " " ^ Int.to_string x ^ " not found when converting to whnf")
    end
  | Lambda (_, x, x_tp, body) -> Lambda (x, x_tp, body)
  | Product (_, x, x_tp, body) -> Product (x, x_tp, body)
  | TypeArrow (tp1, tp2) -> Product(-1, tp1, tp2)
  | App (t1, t2) ->
    begin match to_whnf t1 env with
    | Neu (x, ts) -> Neu (x, (t2 :: ts))
    | Neu_with_Hole (x, tp, ts) -> Neu_with_Hole (x, tp, (t2 :: ts))
    | Lambda (x, _, body) -> to_whnf (substitute body (VarMap.singleton x t2)) env
    | _ -> failwith ("Expected Neu or Lambda when reducing Application " ^ term_to_string t1 ^ " with whnf " ^ term_to_string t2)
    end
  | Hole (nm, tp) -> Neu_with_Hole (nm, tp, [])
  (* Ask PPO, potrzebujemy fresh_var? A jak tak to jak to zrobić bo chwilowa implementacja chyba na to nie pozwala *)
  (* Użyć nowego środowiska, wygenerować świeżą zmienną i zrobić podstawienie *)
  | Let (_, var, t1, tp_t1, t2) ->
    let _ = add_to_termEnv env var (Transparent (t1, tp_t1)) in
    (* zrobić funkcję subst dla whnf i tu podstawić po sprowadzeniu do whnf *)
    let t2 = to_whnf t2 env in
    let t2 = substitute_whnf t2 (VarMap.singleton var t1) in
    let _ = rm_from_termEnv env var in
    t2
    (* let x = A in B ... to whnf B -> zCDx ... subst B {x -> A}*)
    (* let x = A in B ... to whnf B -> Lambda(y, ..., x) ... subst B {x -> A}*)
  (* Ask PPO *)
  (* For let (let x = A in B) add A to env and recurse on B, *) 
  end


let rec equiv (t1: term) (t2: term) (env: termEnv): bool =
  match (to_whnf t1 env, to_whnf t2 env) with
  | (Type, Type) -> true
  | (Kind, Kind) -> true
  | (Neu (x1, ts1), Neu (x2, ts2))-> 
    x1 = x2 
    && List.length ts1 = List.length ts2 
    && List.for_all2 (fun x y -> equiv x y env) ts1 ts2
  (* Tutaj możemy zrobić jeśli jest ta sama dziura, jeśli różnią się nazwą to powiedzmy o tym *)
  (* Jeżeli dwie dziury mają różne argumenty to pokazać jakie są użytkownikowi i nadal zwracamy true *)
  | (Neu_with_Hole (_, tp1, ts1), Neu_with_Hole (_, tp2, ts2)) ->
    equiv tp1 tp2 env
    && List.length ts1 = List.length ts2 
    && List.for_all2 (fun x y -> equiv x y env) ts1 ts2
  | (Lambda (x1, x1_tp, body1), Lambda (x2, x2_tp, body2)) ->
    if equiv x1_tp x2_tp env then
      let fresh_var = fresh_var () in
      let body1' = substitute body1 (VarMap.singleton x1 (Var ("", fresh_var))) in
      let body2' = substitute body2 (VarMap.singleton x2 (Var ("", fresh_var))) in
      equiv body1' body2' env
    else
      false
  | (Product (x1, x1_tp, body1), Product (x2, x2_tp, body2)) ->
    if equiv x1_tp x2_tp env then
      let fresh_var = fresh_var () in
      let body1' = substitute body1 (VarMap.singleton x1 (Var ("", fresh_var))) in
      let body2' = substitute body2 (VarMap.singleton x2 (Var ("", fresh_var))) in
      equiv body1' body2' env
    else
      false
  (* Nie kończymy błędem tylko lecimy dalej po wypisaniu *)
  | (Neu_with_Hole (nm, _, _), _) -> failwith ("Hole " ^ nm ^ " is expected to be equal to " ^ (term_to_string t2))
  | (_, Neu_with_Hole (nm, _, _)) -> failwith ("Hole " ^ nm ^ " is expected to be equal to " ^ (term_to_string t1))
  | _ -> false

let rec infer_type ((_, termEnv) as env : env) ({pos; data = t}: ParserAst.uTerm) : (term * term) = 
  match t with 
  | Type -> (Type, Kind)
  | Kind -> (Kind, Triangle)
  | Var x -> 
    begin match find_opt_in_env env x with
    | Some (y, (Opaque tp | (Transparent (_, tp)))) -> (Var (x, y), tp) 
    | None -> failwith (create_error_msg pos ("Variable " ^ x ^ " not found"))
    end
  | Lambda (_, None, _) -> failwith (create_error_msg pos "Can't infer the type of lambda with omitted argument type")
  | Lambda (x, Some tp, t) -> 
    let (tp, tp_of_tp) = infer_type env tp in
    begin match tp_of_tp with
      | Type | Kind | Triangle -> 
        let fresh_var = add_to_env env x (Opaque tp) in
        let (body, body_tp) = infer_type env t in
        let _ = rm_from_env env x in
        (Lambda (x, fresh_var, tp, body) , Product (x, fresh_var, tp, body_tp))
      | _ -> failwith (create_error_msg pos "The type of Lambda argument type must be either Type or Kind")
    end
  | Product (x, tp, t) ->
    let (tp, tp_of_tp) = infer_type env tp in
    begin match tp_of_tp with
      | Type | Kind | Triangle -> 
        let fresh_var = add_to_env env x (Opaque tp) in
        let (body, body_tp) = infer_type env t in
        let _ = rm_from_env env x in
        begin match body_tp with
        | Type | Kind -> 
          (Product (x, fresh_var, tp, body) , body_tp)
        | _ -> failwith (create_error_msg pos "The type of Product body type must be either Type or Kind")
        end
      | _ -> failwith (create_error_msg pos "The type of Product argument type must be either Type or Kind")
    end
  | TypeArrow (tp1, tp2) ->
    let (tp1, tp_of_tp1) = infer_type env tp1 in
    begin match tp_of_tp1 with
      | Type | Kind -> 
        let (tp2, tp_of_tp2) = infer_type env tp2 in
        begin match tp_of_tp2 with
        | Type | Kind -> 
          (TypeArrow (tp1, tp2) , tp_of_tp2)
        | _ -> failwith (create_error_msg pos "The type of Type Arrow body type must be either Type or Kind")
        end
      | _ -> failwith (create_error_msg pos "The type of Type Arrow argument type must be either Type or Kind")
    end
  | App (t1, t2) ->
    let (t1, t1_tp) = infer_type env t1 in
    begin match to_whnf t1_tp termEnv with
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
    let fresh_var = add_to_env env x (Transparent (t1, tp_t1)) in
    let (t2, tp_t2) = infer_type env t2 in
    let _ = rm_from_env env x in
    Let (x, fresh_var, t1, tp_t1, t2), (substitute tp_t2 (VarMap.singleton fresh_var t1))
  | LetDef (x, t1) -> 
    let (t1, tp_t1) = infer_type env t1 in
    let _ = add_to_env env x (Transparent (t1, tp_t1)) in
    t1, tp_t1
  | Lemma (x, t1, t2) -> 
    let (t1, tp_t1) = infer_type env t1 in
    let fresh_var = add_to_env env x (Opaque tp_t1) in
    let (t2, tp_t2) = infer_type env t2 in
    let _ = rm_from_env env x in
    (App (Lambda (x, fresh_var, tp_t1, t2), t1), (substitute tp_t2 (VarMap.singleton fresh_var t1)))
  | LemmaDef(x, t1) -> 
    let (t1, tp_t1) = infer_type env t1 in
    let _ = add_to_env env x (Opaque tp_t1) in
    t1, tp_t1
  | Hole x -> failwith (create_error_msg pos "Trying to infer the type of a Hole " ^ x)

    
and check_type ((_, termEnv) as env : env) ({pos; data = t} as term: ParserAst.uTerm) (tp: term) : term =
  match t with 
  | Type | Var _ | App _ | Product _ | TermWithTypeAnno _ | TypeArrow _ -> 
    let (t, t_tp) = infer_type env term in
    if equiv tp t_tp termEnv then t else failwith (create_error_msg pos (create_error_msg pos "Type mismatch"))
  | Lambda (x, None, body) -> 
    begin match to_whnf tp termEnv with
    | Product (y, y_tp, body_tp) -> 
      let fresh_var = add_to_env env x (Opaque y_tp) in
      let body' = check_type env body (substitute body_tp (VarMap.singleton y y_tp)) in 
      let _ = rm_from_env env x in
      Lambda (x, fresh_var, y_tp, body')
    | _ -> failwith (create_error_msg pos "The type of Lambda must be a Product")
    end
  | Lambda (x, Some x_tp, body) ->
    let _ = print_endline ((uterm_to_string term) ^ " : " ^ term_to_string tp) in
    (* let _ = print_endline ((uterm_to_string body) ^ " : " ^ term_to_string tp) in *)
    begin match (check_type env {pos = pos; data = (Lambda (x, None, body))} tp) with
    | Lambda (_, _, arg_tp, _) as lambda -> 
      (* let _ = print_endline (term_to_string lambda) in *)
      let (x_tp, _) = infer_type env x_tp in
      if equiv x_tp arg_tp termEnv then lambda else failwith "Type mismatch"
    | _ -> failwith (create_error_msg pos "Lambda must be lambda lolz")
    end
  | Kind -> failwith (create_error_msg pos "Kind doesn't have a type")
  | Let (x, t1, t2) -> 
    let (t1, tp_t1) = infer_type env t1 in
    let fresh_var = add_to_env env x (Transparent (t1, tp_t1)) in
    let t2 = check_type env t2 tp in
    let _ = rm_from_env env x in
    Let (x, fresh_var, t1, tp_t1, t2)
  | Lemma (x, t1, t2) -> 
    let (t1, tp_t1) = infer_type env t1 in
    let fresh_var = add_to_env env x (Opaque tp_t1) in
    let t2 = check_type env t2 tp in
    let _ = rm_from_env env x in
    App (Lambda (x, fresh_var, tp_t1, t2), t1)
  (* Ask PPO *)
  (* wypisać środowisko i typ który przypisaliśmy dziurze *)
  (* | Hole nm -> failwith (create_error_msg pos ("Hole " ^ nm ^ " is expected to have type: " ^ term_to_string tp)) *)
  | Hole nm -> Hole (nm, tp)
  | LemmaDef (_, t)   | LetDef (_, t) -> 
    (* let _ = print_endline ((uterm_to_string t) ^ " : " ^ term_to_string tp) in *)
    check_type env t tp
    (* let (t, t_tp) = infer_type env t in
    if equiv tp t_tp termEnv then t else failwith (create_error_msg pos (create_error_msg pos "Type mismatch")) *)
    (* let (_, t2_tp) = infer_type env t2 in
    let _ = print_endline (term_to_string t2_tp) in failwith "" *)

  
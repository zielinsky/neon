open Ast
open Env
open List

type name = string
type builtInFunction = tp * (whnf -> term)

let int_add (w: whnf) : term =
  match w with
  | Neu (_, _, rev_args) ->
    if length rev_args <> 2 then failwith "Expected 2 arguments to int_add"
    else
      let arg1 = hd rev_args in
      let arg2 = hd (tl rev_args) in
      (match arg1, arg2 with
       | IntLit n1, IntLit n2 -> IntLit (n1 + n2)
       | _ -> failwith "Expected two integer literals")
  | _ -> failwith "Unexpected case"

let int_sub (w: whnf) : term =
  match w with
  | Neu (_, _, rev_args) ->
    if length rev_args <> 2 then failwith "Expected 2 arguments to int_sub"
    else
      let arg1 = hd rev_args in
      let arg2 = hd (tl rev_args) in
      (match arg1, arg2 with
       | IntLit n1, IntLit n2 -> IntLit (n1 - n2)
       | _ -> failwith "Expected two integer literals")
  | _ -> failwith "Unexpected case"

let int_mul (w: whnf) : term =
  match w with
  | Neu (_, _, rev_args) ->
    if length rev_args <> 2 then failwith "Expected 2 arguments to int_mul"
    else
      let arg1 = hd rev_args in
      let arg2 = hd (tl rev_args) in
      (match arg1, arg2 with
       | IntLit n1, IntLit n2 -> IntLit (n1 * n2)
       | _ -> failwith "Expected two integer literals")
  | _ -> failwith "Unexpected case"

let int_div (w: whnf) : term =
  match w with
  | Neu (_, _, rev_args) ->
    if length rev_args <> 2 then failwith "Expected 2 arguments to int_div"
    else
      let arg1 = hd rev_args in
      let arg2 = hd (tl rev_args) in
      (match arg1, arg2 with
       | IntLit n1, IntLit n2 -> IntLit (n1 / n2)
       | _ -> failwith "Expected two integer literals")
  | _ -> failwith "Unexpected case"

let builtIn_functions : (name, builtInFunction) Hashtbl.t = Hashtbl.create 10

let () =
  Hashtbl.add builtIn_functions "_builtin_add" (TypeArrow (IntType, TypeArrow (IntType, IntType)), int_add);
  Hashtbl.add builtIn_functions "_builtin_sub" (TypeArrow (IntType, TypeArrow (IntType, IntType)), int_sub);
  Hashtbl.add builtIn_functions "_builtin_mul" (TypeArrow (IntType, TypeArrow (IntType, IntType)), int_mul);
  Hashtbl.add builtIn_functions "_builtin_div" (TypeArrow (IntType, TypeArrow (IntType, IntType)), int_div)

let load_builtins env =
  let add_builtin name (ty, _) env =
    let _ = Env.add_to_env env name (Opaque ty) in ()
  in
  Hashtbl.iter (fun name ty_func -> add_builtin name ty_func env) builtIn_functions;
  env
;;

let eval_builtin (name : name) (w: whnf) : term option =
  let f = Hashtbl.find_opt builtIn_functions name in 
  match f with
  | Some (_, f) -> begin
      try Some (f w)
      with _ -> None
    end
  | None -> None
;;
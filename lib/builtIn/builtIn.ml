open Ast
open Env
open List

type name = string
type builtInFunction = tp * (whnf -> term option)

let int_add (w : whnf) : term option =
  match w with
  | Neu (_, _, rev_args) -> (
      if length rev_args <> 2 then None
      else
        let arg1 = hd rev_args in
        let arg2 = hd (tl rev_args) in
        match (arg1, arg2) with
        | IntLit n1, IntLit n2 -> Some (IntLit (n1 + n2))
        | _ -> None)
  | _ -> None

let int_sub (w : whnf) : term option =
  match w with
  | Neu (_, _, rev_args) -> (
      if length rev_args <> 2 then None
      else
        let arg1 = hd rev_args in
        let arg2 = hd (tl rev_args) in
        match (arg1, arg2) with
        | IntLit n1, IntLit n2 -> Some (IntLit (n1 - n2))
        | _ -> None)
  | _ -> None

let int_mul (w : whnf) : term option =
  match w with
  | Neu (_, _, rev_args) -> (
      if length rev_args <> 2 then None
      else
        let arg1 = hd rev_args in
        let arg2 = hd (tl rev_args) in
        match (arg1, arg2) with
        | IntLit n1, IntLit n2 -> Some (IntLit (n1 * n2))
        | _ -> None)
  | _ -> None

let int_div (w : whnf) : term option =
  match w with
  | Neu (_, _, rev_args) -> (
      if length rev_args <> 2 then None
      else
        let arg1 = hd rev_args in
        let arg2 = hd (tl rev_args) in
        match (arg1, arg2) with
        | IntLit n1, IntLit n2 -> Some (IntLit (n1 / n2))
        | _ -> None)
  | _ -> None

let io_read_int (w : whnf) : term option =
  match w with
  | Neu (_, _, rev_args) ->
      if length rev_args <> 0 then None else Some (IntLit (read_int ()))
  | _ -> None

let io_print_int (w : whnf) : term option =
  match w with
  | Neu (_, _, rev_args) -> (
      if length rev_args <> 1 then None
      else
        let arg = hd rev_args in
        match arg with
        | IntLit n ->
            print_int n;
            print_newline ();
            Some (IntLit n)
        | _ -> None)
  | _ -> None

let builtIn_functions : (name, builtInFunction) Hashtbl.t = Hashtbl.create 10

let () =
  Hashtbl.add builtIn_functions "_builtin_add"
    (TypeArrow (IntType, TypeArrow (IntType, IntType)), int_add);
  Hashtbl.add builtIn_functions "_builtin_sub"
    (TypeArrow (IntType, TypeArrow (IntType, IntType)), int_sub);
  Hashtbl.add builtIn_functions "_builtin_mul"
    (TypeArrow (IntType, TypeArrow (IntType, IntType)), int_mul);
  Hashtbl.add builtIn_functions "_builtin_div"
    (TypeArrow (IntType, TypeArrow (IntType, IntType)), int_div)

let load_builtins env =
  let add_builtin name (ty, _) env =
    let _ = Env.add_to_env env name (Opaque ty) in
    ()
  in
  Hashtbl.iter
    (fun name ty_func -> add_builtin name ty_func env)
    builtIn_functions;
  env

let eval_builtin (name : name) (w : whnf) : term option =
  let f = Hashtbl.find_opt builtIn_functions name in
  match f with Some (_, f) -> f w | None -> None

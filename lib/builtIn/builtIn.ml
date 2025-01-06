open Ast
open Env
open List
type name = string
type builtInFunction = name * tp * term

let int_add (x: term) (y: term) : term = 
  match x, y with
  | IntLit x, IntLit y -> IntLit (x + y)
  | _ -> raise (Failure "Type error in int_add")

let int_sub (x: term) (y: term) : term =
  match x, y with
  | IntLit x, IntLit y -> IntLit (x - y)
  | _ -> raise (Failure "Type error in int_sub")

let int_mul (x: term) (y: term) : term =
  match x, y with
  | IntLit x, IntLit y -> IntLit (x * y)
  | _ -> raise (Failure "Type error in int_mul")

let int_div (x: term) (y: term) : term =
  match x, y with
  | IntLit x, IntLit y -> IntLit (x / y)
  | _ -> raise (Failure "Type error in int_div")

let load_builtins env =
  let add_builtin name ty =
    let _ = Env.add_to_env env name (Opaque ty) in ()
  in
  let builtinFunctions = [
      "_builtin_add", TypeArrow (IntType, TypeArrow (IntType, IntType)), int_add;
      "_builtin_sub", TypeArrow (IntType, TypeArrow (IntType, IntType)), int_sub;
      "_builtin_mul", TypeArrow (IntType, TypeArrow (IntType, IntType)), int_mul;
      "_builtin_div", TypeArrow (IntType, TypeArrow (IntType, IntType)), int_div;
  ] in 
  fold_left (fun env (name, ty, _) -> add_builtin name ty; env) env builtinFunctions
;;
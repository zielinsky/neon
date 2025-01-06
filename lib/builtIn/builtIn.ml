open Ast
open Env

let load_builtins env =
  let add_builtin name ty =
    let _ = Env.add_to_env env name (Opaque ty) in ()
  in
  add_builtin "_builtin_add" (TypeArrow (IntType, TypeArrow (IntType, IntType)));
  add_builtin "_builtin_sub" (TypeArrow (IntType, TypeArrow (IntType, IntType)));
  add_builtin "_builtin_mul" (TypeArrow (IntType, TypeArrow (IntType, IntType)));
  add_builtin "_builtin_div" (TypeArrow (IntType, TypeArrow (IntType, IntType)));
;;
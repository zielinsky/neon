type typeCName = string
type dataCName = string

module Var : sig
  type t

  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
  val of_int : int -> t
  val to_int : t -> int
  val to_string : t -> string
end = struct
  type t = int

  let compare = Int.compare
  let equal = Int.equal
  let hash = Int.hash
  let to_string = Int.to_string
  let of_int x = x
  let to_int x = x
end

type term =
  | Type
  | Kind
  | Var of string * Var.t
  | IntType
  | StringType
  | BoolType
  | IntLit of int
  | StringLit of string
  | BoolLit of bool
  | Lambda of string * Var.t * tp * term
  | Product of string * Var.t * tp * tp
  | App of term * term
  | Hole of string * tp
  | Let of string * Var.t * term * tp * term
  | TypeArrow of tp * tp
  | Case of term * matchPat list

and constructorDef = { cname : string; telescope : telescope }
and telescope = Empty | Cons of string * Var.t * tp * telescope
and matchPat = pattern * term
and pattern = PatWild | PatCon of dataCName * (string * Var.t) list
and tp = term

module VarMap = Map.Make (Var)

type sub_map = term VarMap.t

let add_to_sub_map (var : Var.t) (t : term) (sub_map : sub_map) : sub_map =
  VarMap.add var t sub_map

let singleton_sub_map (var : Var.t) (t : term) : sub_map =
  VarMap.singleton var t

let find_opt_sub_map (var : Var.t) (sub_map : sub_map) : term option =
  VarMap.find_opt var sub_map

let of_list_sub_map (xs : (Var.t * term) list) : sub_map = VarMap.of_list xs
let empty_sub_map : sub_map = VarMap.empty
let dataCName_of_string (s : string) : dataCName = s
let typeCName_of_string (s : string) : typeCName = s
let dataCName_to_string (s : dataCName) : string = s
let typeCName_to_string (s : typeCName) : string = s

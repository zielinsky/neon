type sub_map

val add_to_sub_map : Ast.Var.t -> Ast.term -> sub_map -> sub_map
val singleton_sub_map : Ast.Var.t -> Ast.term -> sub_map
val find_opt_sub_map : Ast.Var.t -> sub_map -> Ast.term option
val of_list_sub_map : (Ast.Var.t * Ast.term) list -> sub_map
val empty_sub_map : sub_map
val substitute : Ast.term -> sub_map -> Ast.term
val substitute_whnf : Ast.whnf -> sub_map -> Ast.whnf
val substitute_in_telescope : Ast.telescope -> sub_map -> Ast.telescope

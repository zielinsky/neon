type sub_map

val add_to_sub_map : Core.Var.t -> Core.term -> sub_map -> sub_map
val singleton_sub_map : Core.Var.t -> Core.term -> sub_map
val find_opt_sub_map : Core.Var.t -> sub_map -> Core.term option
val of_list_sub_map : (Core.Var.t * Core.term) list -> sub_map
val empty_sub_map : sub_map
val substitute : Core.term -> sub_map -> Core.term
val substitute_in_telescope : Core.telescope -> sub_map -> Core.telescope

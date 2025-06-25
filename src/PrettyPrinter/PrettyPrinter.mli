val term_to_string : Core.term -> string
val uterm_to_string : Raw.term -> string
val whnf_to_string : Core.whnf -> string
val print : Core.term * Core.tp -> unit
val print_def : Raw.term -> unit
val print_def_with_type : Raw.term -> Core.tp -> unit
val print_def_with_body_and_type : Raw.term -> Core.term -> Core.tp -> unit
val pattern_to_string : Core.pattern -> string
val telescope_to_string : Core.telescope -> string

val term_to_string : Core.term -> string
val uterm_to_string : Raw.uTerm -> string
val whnf_to_string : Core.whnf -> string
val print : Core.term * Core.tp -> unit
val print_def : Raw.uTerm -> unit
val pattern_to_string : Core.pattern -> string
val telescope_to_string : Core.telescope -> string

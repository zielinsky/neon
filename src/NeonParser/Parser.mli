type fname = string
type input = string

val parse_file : fname -> Raw.program
val parse_string : input -> Raw.program

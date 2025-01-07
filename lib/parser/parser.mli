type fname = string
type input = string

val parse_file : fname -> ParserAst.program
val parse_string : input -> ParserAst.program

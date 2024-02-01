%token TYPE KIND LAMBDA PRODUCT APP TERMWITHYPEANNO LET LEMMA EQUAL IN ARROW TYPE_ARROW
%token<string> VAR HOLE
%token BR_OPN BR_CLS
%token ASTERISK COMMA COLON IN EQUAL
%token EOF

%type<ParserAst.program> program
%start program


%{

open ParserAst

let current_pos () =
  let start_p = symbol_start_pos () in
  let end_p   = symbol_end_pos () in
  { start  = start_p
  ; length = end_p.pos_cnum - start_p.pos_cnum
  }

let make data =
  { pos  = current_pos ()
  ; data = data
  }

%}

%%

functions
: single_arg_function { $1 }
| multi_arg_function { $1 }
;

single_arg_function
: VAR ARROW expression { make (Lambda ($1, None, $3)) }
| VAR COLON expression ARROW expression { make (Lambda ($1, Some $3, $5)) }
| BR_OPN VAR COLON expression BR_CLS ARROW expression { make (Lambda ($2, Some $4, $7)) }
;

multi_arg_function
: VAR multi_arg_function {make (Lambda ($1, None, $2))}
| VAR ARROW expression {make (Lambda ($1, None, $3))}
| BR_OPN VAR COLON expression BR_CLS multi_arg_function {make (Lambda ($2, Some $4, $6))}
| BR_OPN VAR COLON expression BR_CLS ARROW expression {make (Lambda ($2, Some $4, $7))}
;

products
: single_arg_product { $1 }
| multi_arg_product { $1 }
;

single_arg_product
: VAR COLON expression ARROW expression { make (Product ($1, $3, $5)) }
| BR_OPN VAR COLON expression BR_CLS ARROW expression { make (Product ($2, $4, $7)) }
;

multi_arg_product
: BR_OPN VAR COLON expression BR_CLS multi_arg_product {make (Product ($2, $4, $6))}
| BR_OPN VAR COLON expression BR_CLS ARROW expression {make (Product ($2, $4, $7))}
;

expression
: TYPE { make (Type) }
| KIND { make (Kind) }
| VAR  { make (Var $1) }
| HOLE { make (Hole $1) }
| LET VAR EQUAL expression IN expression {make (Let ($2, $4, $6)) }
| LEMMA VAR EQUAL expression IN expression { make (Lemma ($2, $4, $6)) }
| LAMBDA functions { $2 }
| PRODUCT products { $2 }
| expression COLON expression {make (TermWithTypeAnno ($1, $3)) }
| expression TYPE_ARROW expression {make (TypeArrow ($1, $3)) }
| BR_OPN expression BR_CLS { $2 }
| expression BR_OPN expression BR_CLS { make (App ($1, $3)) }

let_def
: VAR EQUAL expression { make (LetDef ($1, $3)) }
| VAR let_args  { make (LetDef ($1, $2)) }
| VAR COLON expression EQUAL expression { make (TermWithTypeAnno(make (LetDef ($1, $5)), $3)) }
| BR_OPN VAR COLON expression BR_CLS EQUAL expression { make (TermWithTypeAnno(make (LetDef ($2, $7)), $4)) }
;

let_args
: VAR EQUAL expression { make (Lambda ($1, None, $3)) }
| VAR let_args {make (Lambda ($1, None, $2))}
| BR_OPN VAR COLON expression BR_CLS EQUAL expression { make (Lambda ($2, Some $4, $7)) }
| BR_OPN VAR COLON expression BR_CLS let_args { make (Lambda ($2, Some $4, $6)) }

lemma_def
: VAR EQUAL expression { make (LemmaDef ($1, $3)) }
| VAR lemma_args  { make (LemmaDef ($1, $2)) }
| VAR COLON expression EQUAL expression { make (TermWithTypeAnno(make (LemmaDef ($1, $5)), $3)) }
| BR_OPN VAR COLON expression BR_CLS EQUAL expression { make (TermWithTypeAnno(make (LemmaDef ($2, $7)), $4)) }
;

lemma_args
: VAR EQUAL expression { make (Lambda ($1, None, $3)) }
| VAR lemma_args {make (Lambda ($1, None, $2))}
| BR_OPN VAR COLON expression BR_CLS EQUAL expression { make (Lambda ($2, Some $4, $7)) }
| BR_OPN VAR COLON expression BR_CLS lemma_args { make (Lambda ($2, Some $4, $6)) }

expression_definition
: LET let_def { $2 }
| LEMMA lemma_def { $2 }
;

/* ========================================================================= */

expression_list
: /* empty */            { [] }
| expression_definition expression_list { $1 :: $2 }
;


/* ========================================================================= */

program
: expression_list EOF { $1 }
;

%%
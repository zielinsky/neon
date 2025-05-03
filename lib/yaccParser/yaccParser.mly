%token TYPE KIND LAMBDA PRODUCT APP TERMWITHYPEANNO LET LEMMA EQUAL IN ARROW TYPE_ARROW COMMA
%token INT_TYPE STRING_TYPE BOOL_TYPE
%token <int> INT_LIT
%token <string> STRING_LIT
%token <bool> BOOL_LIT
%token<string> VAR HOLE
%token BR_OPN BR_CLS
%token ASTERISK COMMA COLON IN EQUAL
%token EOF
%token ADTDEF
%token BAR
%token MATCH WITH WILDCARD

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

let makeApp exp arg_list =
  match arg_list with 
  | [] -> failwith "cannot apply without any argument"
  | arg::arg_list -> List.fold_left (fun acc elem -> make (App (acc, elem))) (make (App (exp, arg))) arg_list
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

application
: expression BR_OPN application_args BR_CLS { makeApp $1 $3 }
;

application_args
: expression { [$1] }
| expression COMMA application_args { $1 :: $3 } 
;

telescopes
:                                               { Empty }
| BR_OPN VAR COLON expression BR_CLS telescopes { Cons ($2, $4, $6) }
;

constructor_def
: VAR telescopes { {cname = $1; telescope = $2;} }
;

constructor_def_list
: BAR constructor_def constructor_def_list { $2 :: $3 }
| BAR constructor_def { [$2] }
;

adt_def
: ADTDEF VAR telescopes EQUAL constructor_def_list{ make (ADTDecl ($2, $3, $5)) }
| ADTDEF VAR telescopes { make (ADTSig ($2, $3)) }
;

pattern_list
: pattern { [$1] }
| pattern pattern_list { $1 :: $2 }
;

pattern
: BAR WILDCARD TYPE_ARROW expression { PatWild, $4 }
| BAR VAR BR_OPN pattern_var_list BR_CLS TYPE_ARROW expression { PatCon ($2, $4), $7 }
;

pattern_var_list
: VAR { [$1] }
| VAR COMMA pattern_var_list { $1 :: $3 }
;

expression
: TYPE { make (Type) }
| KIND { make (Kind) }
| INT_TYPE       { make IntType }
| STRING_TYPE    { make StringType }
| BOOL_TYPE      { make BoolType }
| INT_LIT        { make (IntLit $1) }
| STRING_LIT     { make (StringLit $1) }
| BOOL_LIT       { make (BoolLit $1) }
| VAR  { make (Var $1) }
| HOLE { make (Hole $1) }
| LAMBDA functions { $2 }
| PRODUCT products { $2 }
| LET VAR EQUAL expression IN expression {make (Let ($2, $4, $6)) }
| LEMMA VAR EQUAL expression IN expression { make (Lemma ($2, $4, $6)) }
| MATCH expression WITH pattern_list { make (Case ($2, $4)) }
| expression TYPE_ARROW expression {make (TypeArrow ($1, $3)) }
| application { $1 }
| BR_OPN expression BR_CLS { $2 }

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
| adt_def        { $1 }
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
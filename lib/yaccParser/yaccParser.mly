%token TYPE KIND LAMBDA PRODUCT APP TERMWITHYPEANNO LET LEMMA EQUAL IN ARROW 
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

/* ========================================================================= */

program
: expression EOF { [$1] }
;

expression
: TYPE { make (Type) }
| KIND { make (Kind) }
| VAR  { make (Var $1) }
| HOLE { make (Hole $1) }
| LAMBDA VAR COLON expression ARROW expression {make  (Lambda ($2, (Some $4), $6)) }
| LAMBDA VAR ARROW expression {make (Lambda ($2, None, $4)) }
| PRODUCT VAR COLON expression ARROW expression {make (Product ($2, $4, $6)) }
| expression COLON expression {make (TermWithTypeAnno ($1, $3)) }
| LET VAR EQUAL expression IN expression {make (Let ($2, $4, $6)) }
| LEMMA VAR EQUAL expression IN expression { make (Lemma ($2, $4, $6)) }
| BR_OPN expression BR_CLS { $2 }
| expression expression { make (App ($1, $2)) }
;

%%
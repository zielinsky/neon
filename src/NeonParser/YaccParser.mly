%{
open Raw

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
  | arg :: arg_list ->
      List.fold_left (fun acc elem -> make (App (acc, elem)))
        (make (App (exp, arg))) arg_list
%}

/* ------------------------------------------------------------------------- */
/*  Tokens                                                                   */
/* ------------------------------------------------------------------------- */
%token TYPE KIND LAMBDA PRODUCT APP TERMWITHYPEANNO LET LEMMA EQUAL IN ARROW TYPE_ARROW COMMA
%token INT_TYPE STRING_TYPE BOOL_TYPE
%token <int>    INT_LIT
%token <string> STRING_LIT
%token <bool>   BOOL_LIT
%token <string> VAR HOLE ADTCON
%token BR_OPN BR_CLS
%token ASTERISK COLON EQUAL
%token EOF
%token ADTDEF
%token BAR
%token MATCH WITH WILDCARD
%token IF THEN ELSE
%token EQUALITY
%token <string> OPERATOR

/* ------------------------------------------------------------------------- */
/*  Entry point                                                              */
/* ------------------------------------------------------------------------- */
%type <Raw.program> program
%start program

/* ------------------------------------------------------------------------- */
/*  Grammar                                                                  */
/* ------------------------------------------------------------------------- */
%left COMMA BAR
%left APP
%left OPERATOR
%nonassoc EQUALITY
%right TYPE_ARROW
%right ARROW
%right LAMBDA PRODUCT

%%

/* ─────────────────────────  Functions (lambda abstractions) ────────────── */
functions
: single_arg_function { $1 }
| multi_arg_function  { $1 }
;

single_arg_function
: VAR ARROW expression                               { make (Lambda ($1, None, $3)) }
| VAR COLON expression ARROW expression              { make (Lambda ($1, Some $3, $5)) }
| BR_OPN VAR COLON expression BR_CLS ARROW expression{ make (Lambda ($2, Some $4, $7)) }
;

multi_arg_function
: VAR multi_arg_function                                { make (Lambda ($1, None, $2)) }
| VAR ARROW expression                                  { make (Lambda ($1, None, $3)) }
| BR_OPN VAR COLON expression BR_CLS multi_arg_function { make (Lambda ($2, Some $4, $6)) }
| BR_OPN VAR COLON expression BR_CLS ARROW expression   { make (Lambda ($2, Some $4, $7)) }
;

/* ─────────────────────────  Products (Π-types)  ────────────────────────── */
products
: single_arg_product { $1 }
| multi_arg_product { $1 }
;

single_arg_product
: VAR COLON expression ARROW expression               { make (Product ($1, $3, $5)) }
| BR_OPN VAR COLON expression BR_CLS ARROW expression { make (Product ($2, $4, $7)) }
;

multi_arg_product
: BR_OPN VAR COLON expression BR_CLS multi_arg_product { make (Product ($2, $4, $6)) }
| BR_OPN VAR COLON expression BR_CLS ARROW expression  { make (Product ($2, $4, $7)) }
;

/* ─────────────────────────  Telescopes  ─────────────────────────────────── */
telescopes
:                                               { Empty }
| BR_OPN VAR COLON expression BR_CLS telescopes { Cons ($2, $4, $6) }
;

/* ─────────────────────────  Algebraic data types  ──────────────────────── */
constructor_def
: ADTCON telescopes { { cname = $1; telescope = $2 } }
;

constructor_def_list
: BAR constructor_def constructor_def_list { $2 :: $3 }
| BAR constructor_def                      { [$2] }
;

adt_def
: ADTDEF ADTCON telescopes EQUAL constructor_def_list { make (ADTDecl ($2, $3, $5)) }
| ADTDEF ADTCON telescopes                            { make (ADTSig ($2, $3)) }
;

/* ─────────────────────────  Patterns  ───────────────────────────────────── */
pattern_var_list
: VAR                         { [$1] }
| VAR COMMA pattern_var_list  { $1 :: $3 }
;

pattern
: BAR WILDCARD TYPE_ARROW expression                           { PatWild, $4 }
| BAR ADTCON BR_OPN pattern_var_list BR_CLS TYPE_ARROW expression { PatCon ($2, $4), $7 }
;

pattern_list
: pattern              { [$1] }
| pattern pattern_list { $1 :: $2 }
;

/* ─────────────────────────  Application argument list  ─────────────────── */
app_args
: expression                         { [$1] }
| expression COMMA app_args          { $1 :: $3 }
;

/* ========================================================================= */
/*  EXPRESSION GRAMMAR                                                       */
/* ========================================================================= */

/*  lowest layer: atoms  */
atom
: TYPE                     { make Type }
| KIND                     { make Kind }
| INT_TYPE                 { make IntType }
| STRING_TYPE              { make StringType }
| BOOL_TYPE                { make BoolType }
| INT_LIT                  { make (IntLit $1) }
| STRING_LIT               { make (StringLit $1) }
| BOOL_LIT                 { make (BoolLit $1) }
| VAR                      { make (Var $1) }
| ADTCON                   { make (Var $1) }
| HOLE                     { make (Hole $1) }
| BR_OPN expression BR_CLS { $2 }
;

/*  application (left-assoc) */
app
: atom                                   { $1 }
| app BR_OPN app_args BR_CLS             { makeApp $1 $3 }
;

/*  user-defined infix operator (left-assoc) */
op_expr
: app                                    { $1 }
| op_expr OPERATOR app                   { make (App (make (App (make (Var $2), $1)), $3)) }
;

/*  equality, non-assoc */
eq_expr
: op_expr                                { $1 }
| op_expr EQUALITY op_expr               { make (Equality ($1, $3)) }
;

/*  type arrow, right-assoc */
typearrow_expr
: eq_expr                                { $1 }
| eq_expr TYPE_ARROW typearrow_expr      { make (TypeArrow ($1, $3)) }
;

/*  top layer */
expression
: typearrow_expr                                         { $1 }
| LAMBDA functions                                       { $2 }
| PRODUCT products                                       { $2 }
| LET let_in                                             { $2 }
| LEMMA VAR EQUAL expression IN expression               { make (Lemma ($2, $4, $6)) }
| MATCH expression WITH pattern_list                     { make (Case ($2, $4)) }
| IF expression THEN expression ELSE expression          { make (IfExpr ($2, $4, $6)) }
;

/* ========================================================================= */
/*  LET / LEMMA / OPERATOR-LET definitions                                    */
/* ========================================================================= */

let_args
: VAR EQUAL expression                                    { make (Lambda ($1, None, $3)) }
| VAR let_args                                            { make (Lambda ($1, None, $2)) }
| BR_OPN VAR COLON expression BR_CLS EQUAL expression     { make (Lambda ($2, Some $4, $7)) }
| BR_OPN VAR COLON expression BR_CLS let_args             { make (Lambda ($2, Some $4, $6)) }
;

let_def
: VAR EQUAL expression                                     { make (LetDef ($1, $3)) }
| VAR let_args                                             { make (LetDef ($1, $2)) }
| VAR COLON expression EQUAL expression                    { make (TermWithTypeAnno (make (LetDef ($1, $5)), $3)) }
| BR_OPN VAR COLON expression BR_CLS EQUAL expression      { make (TermWithTypeAnno (make (LetDef ($2, $7)), $4)) }
| BR_OPN VAR COLON expression BR_CLS let_args              { make (TermWithTypeAnno (make (LetDef ($2, $6)), $4)) }
/* operator heads */
| BR_OPN OPERATOR BR_CLS EQUAL expression                  { make (LetDef ($2, $5)) }
| BR_OPN OPERATOR BR_CLS let_args                          { make (LetDef ($2, $4)) }
| BR_OPN OPERATOR BR_CLS COLON expression EQUAL expression { make (TermWithTypeAnno (make (LetDef ($2, $7)), $5)) }
;

let_in
: VAR EQUAL expression IN expression                                   { make (Let ($1, $3, $5)) }
| VAR let_args IN expression                                           { make (Let ($1, $2, $4)) }
| VAR COLON expression EQUAL expression IN expression                  { make (TermWithTypeAnno (make (Let ($1, $5, $7)), $3)) }
| BR_OPN VAR COLON expression BR_CLS EQUAL expression IN expression    { make (TermWithTypeAnno (make (Let ($2, $7, $9)), $4)) }
| BR_OPN VAR COLON expression BR_CLS let_args IN expression            { make (TermWithTypeAnno (make (Let ($2, $6, $8)), $4)) }
/* operator heads */
| BR_OPN OPERATOR BR_CLS EQUAL expression IN expression   { make (Let ($2, $5, $7)) }
| BR_OPN OPERATOR BR_CLS let_args IN expression           { make (Let ($2, $4, $6)) }
| BR_OPN OPERATOR BR_CLS COLON expression EQUAL expression IN expression { make (TermWithTypeAnno (make (Let ($2, $7, $9)), $5)) }
;

lemma_args
: VAR EQUAL expression                                    { make (Lambda ($1, None, $3)) }
| VAR lemma_args                                          { make (Lambda ($1, None, $2)) }
| BR_OPN VAR COLON expression BR_CLS EQUAL expression     { make (Lambda ($2, Some $4, $7)) }
| BR_OPN VAR COLON expression BR_CLS lemma_args           { make (Lambda ($2, Some $4, $6)) }
;

lemma_def
: VAR EQUAL expression                                    { make (LemmaDef ($1, $3)) }
| VAR lemma_args                                          { make (LemmaDef ($1, $2)) }
| VAR COLON expression EQUAL expression                   { make (TermWithTypeAnno (make (LemmaDef ($1, $5)), $3)) }
| BR_OPN VAR COLON expression BR_CLS EQUAL expression     { make (TermWithTypeAnno (make (LemmaDef ($2, $7)), $4)) }
| BR_OPN VAR COLON expression BR_CLS lemma_args           { make (TermWithTypeAnno (make (LemmaDef ($2, $6)), $4)) }
;

/* ========================================================================= */
/*  Top-level                                                                */
/* ========================================================================= */
expression_definition
: LET let_def   { $2 }
| LEMMA lemma_def { $2 }
| adt_def         { $1 }
;

expression_list
: /* empty */                               { [] }
| expression_definition expression_list     { $1 :: $2 }
;

program
: expression_list EOF { $1 }
;

%%

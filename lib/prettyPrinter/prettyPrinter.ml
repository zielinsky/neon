open Ast
open ParserAst
open SmartPrint

let rec pp_term (e : term) : SmartPrint.t =
  let parens_if_app (t : term) =
    match t with App (_, _) -> parens (pp_term t) | _ -> pp_term t
  in
  match e with
  | Type -> !^"type"
  | Kind -> !^"kind"
  | Var (nm, var) -> !^nm
  | Lambda (nm, _, tp_x, body) ->
      nest (!^"λ" ^-^ !^nm ^-^ !^":" ^^ pp_term tp_x ^^ !^"=>" ^^ pp_term body)
  | Product (nm, _, tp_x, body) ->
      nest (!^"Π" ^-^ !^nm ^-^ !^":" ^^ pp_term tp_x ^^ !^"=>" ^^ pp_term body)
  | App (t1, t2) -> nest (parens_if_app t1 ^^ parens_if_app t2)
  | Let (nm, _, t1, tp_t1, t2) ->
      nest
        (!^"let" ^^ !^nm ^^ !^"=" ^^ pp_term t1 ^-^ !^":" ^^ pp_term tp_t1
       ^^ !^"in"
        ^^ nest (pp_term t2))
  | Hole (nm, tp) -> !^nm ^^ !^":" ^^ pp_term tp
  | TypeArrow (tp1, tp2) -> pp_term tp1 ^^ !^"->" ^^ pp_term tp2

let rec term_to_string (t : term) : string = to_string 40 2 (pp_term t)

let print (term, tp) =
  print_endline
    (to_string 40 2
       (pp_term term ^-^ newline
       ^-^ nest (!^"\x1b[1mT:" ^^ pp_term tp ^-^ newline ^-^ !^"\x1b[0m")))

let rec pp_uterm ({ data = e; pos } : uTerm) : SmartPrint.t =
  let parens_if_app ({ data; pos } as t : uTerm) =
    match data with App (_, _) -> parens (pp_uterm t) | _ -> pp_uterm t
  in
  match e with
  | Type -> !^"type"
  | Kind -> !^"kind"
  | Var nm -> !^nm
  | Lambda (nm, tp_x, body) -> (
      match tp_x with
      | Some tp_x ->
          nest
            (!^"λ" ^-^ !^nm ^-^ !^":" ^^ pp_uterm tp_x ^^ !^"=>"
           ^^ pp_uterm body)
      | None -> nest (!^"λ" ^-^ !^nm ^^ !^"=>" ^^ pp_uterm body))
  | Product (nm, tp_x, body) ->
      nest (!^"Π" ^-^ !^nm ^-^ !^":" ^^ pp_uterm tp_x ^^ !^"=>" ^^ pp_uterm body)
  | App (t1, t2) -> nest (parens_if_app t1 ^^ parens_if_app t2)
  | Let (nm, t1, t2) ->
      nest
        (!^"let" ^^ !^nm ^^ !^"=" ^^ pp_uterm t1 ^^ !^"in" ^^ nest (pp_uterm t2))
  | LetDef (nm, t1) -> nest (!^"let" ^^ !^nm ^^ !^"=" ^^ pp_uterm t1)
  | Lemma (nm, t1, t2) ->
      nest
        (!^"lemma" ^^ !^nm ^^ !^"=" ^^ pp_uterm t1 ^^ !^"in"
        ^^ nest (pp_uterm t2))
  | LemmaDef (nm, t1) -> nest (!^"lemma" ^^ !^nm ^^ !^"=" ^^ pp_uterm t1)
  | Hole nm -> !^nm
  | TypeArrow (tp1, tp2) -> pp_uterm tp1 ^^ !^"->" ^^ pp_uterm tp2
  | TermWithTypeAnno (t1, t2) ->
      nest (parens (pp_uterm t1 ^^ !^":" ^^ pp_uterm t2))

let rec uterm_to_string (t : uTerm) : string = to_string 40 2 (pp_uterm t)

let rec pp_whnf (e : whnf) : SmartPrint.t =
  match e with
  | Type -> !^"type"
  | Kind -> !^"kind"
  | Lambda (var, tp_x, body) ->
      nest
        (!^"λ"
        ^-^ !^(Int.to_string var)
        ^-^ !^":" ^^ pp_term tp_x ^^ !^"=>" ^^ pp_term body)
  | Product (var, tp_x, body) ->
      nest
        (!^"Π"
        ^-^ !^(Int.to_string var)
        ^-^ !^":" ^^ pp_term tp_x ^^ !^"=>" ^^ pp_term body)
  | Neu (var, term_list) ->
      !^(Int.to_string var)
      ^^ !^(List.fold_left
              (fun acc term -> "(" ^ term_to_string term ^ ")" ^ acc)
              "" term_list)
  | Neu_with_Hole (nm, tp, term_list) ->
      nest
        (parens
           (!^"Hole " ^^ !^nm ^^ !^" : "
           ^^ !^(term_to_string tp)
           ^^ !^(List.fold_left
                   (fun acc term -> "(" ^ term_to_string term ^ ")" ^ acc)
                   "" term_list)))

let rec whnf_to_string (t : whnf) : string = to_string 40 2 (pp_whnf t)

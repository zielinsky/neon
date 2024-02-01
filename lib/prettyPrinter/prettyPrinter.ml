open Ast
open ParserAst
open SmartPrint

let rec pp (e : term) : SmartPrint.t =
    let parens_if_app (t : term) = 
      match t with
      | App(_, _) -> parens (pp t)
      | _ -> pp t
    in
    match e with
    | Type -> !^"type"
    | Kind -> !^"kind"
    | Var (nm, var) -> !^nm
    | Lambda (nm, _, tp_x, body) ->
        nest
          (!^"λ" ^-^ !^nm ^-^ !^":"
          ^^ pp tp_x
          ^^ !^"=>"
          ^^ pp body)
    | Product (nm, _, tp_x, body) ->
        nest
          (!^"Π" ^-^ !^ nm ^-^ !^":"
          ^^ pp tp_x
          ^^ !^"=>"
          ^^ pp body)
    | App (t1, t2) ->
        nest (parens_if_app t1 ^^ parens_if_app t2)
    | Let (nm, _, t1, tp_t1, t2) ->
        nest
          (!^"let" ^^ !^nm ^^ !^"="
          ^^ pp t1
          ^-^ !^":"
          ^^ pp tp_t1
          ^^ !^"in"
          ^^ nest (pp t2))
    | Hole (nm, tp) -> !^nm ^^ !^":" ^^ pp tp
    | TypeArrow (tp1, tp2) ->
        pp tp1 ^^ !^"->" ^^ pp tp2

let rec term_to_string (t : term) : string = to_string 40 2 (pp t)

(* match t with
   | Type -> "type"
   | Kind -> "kind"
   | Var (nm, var) -> nm
   (* | Var (nm, var) -> nm ^ "@" ^ Int.to_string var *)
   | Lambda (nm, _, tp_x, body) ->
       "(λ" ^ nm ^ ":" ^ term_to_string tp_x ^ " => " ^ term_to_string body ^ ")"
   | Product (nm, _, tp_x, body) ->
       "(Π" ^ nm ^ ":" ^ term_to_string tp_x ^ " => " ^ term_to_string body ^ ")"
   | App (t1, t2) -> "(" ^ term_to_string t1 ^ ") (" ^ term_to_string t2 ^ ")"
   | Let (nm, _, t1, tp_t1, t2) ->
       "(let " ^ nm ^ "=" ^ term_to_string t1 ^ ":" ^ term_to_string tp_t1
       ^ " in\n\t" ^ term_to_string t2
   | Hole (nm, tp) -> nm ^ ":" ^ term_to_string tp
   | TypeArrow (tp1, tp2) ->
       "(" ^ term_to_string tp1 ^ " -> " ^ term_to_string tp2 ^ ")" *)

let rec uterm_to_string ({ pos; data = t } : uTerm) : string =
  match t with
  | Type -> "type"
  | Kind -> "kind"
  | Var nm -> nm
  | Lambda (nm, tp_x, body) -> (
      match tp_x with
      | Some tp_x ->
          "(λ" ^ nm ^ ":" ^ uterm_to_string tp_x ^ " => " ^ uterm_to_string body
          ^ ")"
      | None -> "(λ" ^ nm ^ " => " ^ uterm_to_string body ^ ")")
  | Product (nm, tp_x, body) ->
      "(Π" ^ nm ^ ":" ^ uterm_to_string tp_x ^ " => " ^ uterm_to_string body
      ^ ")"
  | App (t1, t2) -> "(" ^ uterm_to_string t1 ^ ") (" ^ uterm_to_string t2 ^ ")"
  | Let (nm, t1, t2) ->
      "(let " ^ nm ^ "=" ^ uterm_to_string t1 ^ " in\n\t" ^ uterm_to_string t2
  | LetDef (nm, t1) -> "(let " ^ nm ^ "=" ^ uterm_to_string t1
  | Lemma (nm, t1, t2) ->
      "(lemma " ^ nm ^ "=" ^ uterm_to_string t1 ^ " in\n\t" ^ uterm_to_string t2
  | LemmaDef (nm, t1) -> "(lemmaDef " ^ nm ^ "=" ^ uterm_to_string t1
  | Hole nm -> nm
  | TypeArrow (tp1, tp2) ->
      "(" ^ uterm_to_string tp1 ^ " -> " ^ uterm_to_string tp2 ^ ")"
  | TermWithTypeAnno (t1, t2) ->
      "(" ^ uterm_to_string t1 ^ " : " ^ uterm_to_string t2 ^ ")"

let rec whnf_to_string (t : whnf) : string =
  match t with
  | Type -> "type"
  | Kind -> "kind"
  | Neu (var, term_list) ->
      Int.to_string var
      ^ List.fold_left
          (fun acc term -> "(" ^ term_to_string term ^ ")" ^ acc)
          "" term_list
  | Neu_with_Hole (nm, tp, term_list) ->
      "(Hole " ^ nm ^ " : " ^ term_to_string tp ^ ")"
      ^ List.fold_left
          (fun acc term -> "(" ^ term_to_string term ^ ")" ^ acc)
          "" term_list
  | Lambda (var, tp, body) ->
      "(λ" ^ Int.to_string var ^ ":" ^ term_to_string tp ^ " => "
      ^ term_to_string body ^ ")"
  | Product (var, tp, body) ->
      "(Π" ^ Int.to_string var ^ ":" ^ term_to_string tp ^ " => "
      ^ term_to_string body ^ ")"


let print (term, tp) =
    print_endline
        (to_string 40 2 ((pp term) ^-^ newline ^-^ nest (!^"\x1b[1mT:" ^^ (pp tp) ^-^ newline ^-^ !^ "\x1b[0m")))
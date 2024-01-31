open Ast
open ParserAst

let rec term_to_string (t : term) : string =
  match t with
  | Type -> "Type"
  | Kind -> "Kind"
  | Var (nm, _) -> nm
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
      "(" ^ term_to_string tp1 ^ " -> " ^ term_to_string tp2 ^ ")"
  | Triangle -> "Idk how u got here"

let rec uterm_to_string ({ pos; data = t } : uTerm) : string =
  match t with
  | Type -> "Type"
  | Kind -> "Kind"
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

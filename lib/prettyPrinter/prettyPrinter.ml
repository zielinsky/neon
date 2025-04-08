open Ast
open ParserAst
open SmartPrint

let separate_map sep f l =
  let rec aux acc = function
    | [] -> acc
    | [x] -> acc ^^ f x
    | x :: xs -> aux (acc ^^ f x ^^ sep) xs
  in
  aux !^"" l

let rec pp_pattern (p : Ast.pattern) : SmartPrint.t =
  match p with
  | PatWild -> !^"_"
  | PatCon (nm, vars) -> !^nm ^^ !^"(" ^^ separate_map (!^",") (fun (nm, _) -> !^nm) vars ^^ !^")"

let pattern_to_string (p : Ast.pattern) : string = to_string 40 2 (pp_pattern p)

let rec pp_term (e : term) : SmartPrint.t =
  let parens_if_app (t : term) =
    match t with
    | Lambda _ | App _ | Hole (_, (Product _ | TypeArrow _)) -> parens (pp_term t)
    | _ -> pp_term t
  in
  match e with
  | IntType -> !^"Int"
  | StringType -> !^"String"
  | BoolType -> !^"Bool"
  | IntLit n -> !^(string_of_int n)
  | StringLit s -> !^"\"" ^-^ !^s ^-^ !^"\""
  | BoolLit true -> !^"true"
  | BoolLit false -> !^"false"
  | Type -> !^"type"
  | Kind -> !^"kind"
  | Var (nm, var) -> !^"(" ^^ !^nm ^-^ !^":" ^^ !^(string_of_int var) ^^ !^")" 
  | Lambda (nm, var, tp_x, body) ->
      nest (!^"λ" ^-^ !^"(" ^^ !^nm ^-^ !^":" ^^ !^(string_of_int var) ^^ !^")"  ^-^ !^":" ^^ pp_term tp_x ^^ !^"=>" ^^ pp_term body)
  | Product (nm, var, tp_x, body) ->
      nest (!^"Π" ^-^ !^"(" ^^ !^nm ^-^ !^":" ^^ !^(string_of_int var) ^^ !^")"  ^-^ !^":" ^^ pp_term tp_x ^^ !^"=>" ^^ pp_term body)
  | App (t1, t2) -> nest (parens_if_app t1 ^^ parens_if_app t2)
  | Let (nm, _, t1, tp_t1, t2) ->
      nest
        (!^"let" ^^ !^nm ^^ !^"=" ^^ pp_term t1 ^-^ !^":" ^^ pp_term tp_t1
       ^^ !^"in"
        ^^ nest (pp_term t2))
  | Hole (nm, tp) -> !^nm ^-^ !^":" ^^ pp_term tp
  | TypeArrow (tp1, tp2) -> pp_term tp1 ^^ !^"->" ^^ pp_term tp2
  | Case (t, cases) ->
      nest
        (!^"match" ^^ pp_term t ^^ !^"with" ^^ newline
       ^^ nest
            (List.fold_left
               (fun acc ((pattern : Ast.pattern), body) ->
                 acc ^-^ !^"| " ^-^ (pp_pattern pattern) ^-^ !^"=>" ^^ pp_term body ^-^ newline)
                 !^"" cases))
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
  | IntType -> !^"Int"
  | StringType -> !^"String"
  | BoolType -> !^"Bool"
  | IntLit n -> !^(string_of_int n)
  | StringLit s -> !^"\"" ^-^ !^s ^-^ !^"\""
  | BoolLit true -> !^"true"
  | BoolLit false -> !^"false"
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
  | _ -> failwith "TODO Not implemented - PrettyPrinter"

let rec uterm_to_string (t : uTerm) : string = to_string 40 2 (pp_uterm t)

let rec pp_whnf (e : whnf) : SmartPrint.t =
  match e with
  | IntType -> !^"Int"
  | StringType -> !^"String"
  | BoolType -> !^"Bool"
  | IntLit n -> !^(string_of_int n)
  | StringLit s -> !^"\"" ^-^ !^s ^-^ !^"\""
  | BoolLit true -> !^"true"
  | BoolLit false -> !^"false"
  | Type -> !^"type"
  | Kind -> !^"kind"
  | Lambda (nm, var, tp_x, body) ->
      nest (!^"λ" ^-^ !^nm ^-^ !^":" ^^ pp_term tp_x ^^ !^"=>" ^^ pp_term body)
  | Product (nm, var, tp_x, body) ->
      nest (!^"Π" ^-^ !^nm ^-^ !^":" ^^ pp_term tp_x ^^ !^"=>" ^^ pp_term body)
  | Neu (nm, var, term_list) ->
      !^nm
      ^^ List.fold_left
           (fun acc term -> parens (pp_term term) ^^ acc)
           !^"" term_list
  | Neu_with_Hole (nm, tp, term_list) ->
      nest
        (parens (!^"Hole" ^^ !^nm ^^ !^":" ^^ pp_term tp)
        ^^ List.fold_left
             (fun acc term -> parens (pp_term term) ^^ acc)
             !^"" term_list)

let rec whnf_to_string (t : whnf) : string = to_string 40 2 (pp_whnf t)

let print_def ({ pos; data } : uTerm) : unit =
  match data with
  | LetDef (nm, _)
  | LemmaDef (nm, _)
  | TermWithTypeAnno
      ( ( { pos = _; data = LetDef (nm, _) }
        | { pos = _; data = LemmaDef (nm, _) } ),
        _ ) ->
      print_endline ("\x1b[1m" ^ nm ^ "\x1b[0m")  
  | _ -> print_endline "Expected definition at top level"
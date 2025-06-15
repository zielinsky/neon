open SmartPrint

let separate_map sep f l =
  let rec aux acc = function
    | [] -> acc
    | [ x ] -> acc ^^ f x
    | x :: xs -> aux (acc ^^ f x ^-^ sep) xs
  in
  aux !^"" l

let string_of_var (x : Core.Var.t) : string = string_of_int (Core.Var.to_int x)

let rec pp_pattern (p : Core.pattern) : SmartPrint.t =
  match p with
  | PatWild -> !^"_"
  | PatCon (nm, vars) ->
      !^(Core.dataCName_to_string nm)
      ^^ !^"("
      ^^ separate_map !^"," (fun (nm, _) -> !^nm) vars
      ^^ !^")"

let rec pp_uTerm_pattern (p : Raw.pattern) : SmartPrint.t =
  match p with
  | PatWild -> !^"_"
  | PatCon (nm, vars) ->
      !^nm ^-^ !^"(" ^-^ separate_map !^"," (fun nm -> !^nm) vars ^^ !^")"

let pattern_to_string (p : Core.pattern) : string =
  to_string 40 2 (pp_pattern p)

let rec pp_term (e : Core.term) : SmartPrint.t =
  let parens_if_app (t : Core.term) =
    match t with
    | Lambda _ | App _ | Hole (_, (Product _ | TypeArrow _)) ->
        parens (pp_term t)
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
  | Var (nm, var) ->
      !^"(" ^-^ !^nm ^-^ !^"@" ^-^ !^(string_of_var var) ^-^ !^")"
  | Lambda (nm, var, tp_x, body) ->
      nest
        (!^"λ" ^-^ !^"(" ^-^ !^nm ^-^ !^"@"
        ^-^ !^(string_of_var var)
        ^-^ !^":" ^^ pp_term tp_x ^-^ !^")" ^^ !^"=>" ^^ pp_term body)
  | Product (nm, var, tp_x, body) ->
      nest
        (!^"Π" ^-^ !^"(" ^-^ !^nm ^-^ !^"@"
        ^-^ !^(string_of_var var)
        ^-^ !^":" ^^ pp_term tp_x ^-^ !^")" ^^ !^"=>" ^^ pp_term body)
  | App (t1, t2) -> nest (parens_if_app t1 ^^ parens_if_app t2)
  | Let (nm, _, t1, tp_t1, t2) ->
      nest
        (!^"let" ^^ !^nm ^^ !^"=" ^^ pp_term t1 ^-^ !^":" ^^ pp_term tp_t1
       ^^ !^"in"
        ^^ nest (pp_term t2))
  | Hole (nm, tp) -> !^nm ^-^ !^":" ^^ pp_term tp
  | TypeArrow (tp1, tp2) -> pp_term tp1 ^^ !^"->" ^^ pp_term tp2
  | Case (scrut, scrut_tp, var, tp, cases) ->
      let var_str =
        match var with
        | Some (nm, var) ->
            !^" as " ^-^ !^nm ^-^ !^"@" ^-^ !^(string_of_var var)
        | None -> !^""
      in
      let tp_str =
        match tp with Some tp -> !^" return" ^^ pp_term tp | None -> !^""
      in
      nest
        (!^"match" ^^ pp_term scrut ^-^ !^":" ^^ pp_term scrut_tp ^^ var_str
       ^^ tp_str ^^ !^" with" ^^ newline
        ^^ nest
             (List.fold_left
                (fun acc ((pattern : Core.pattern), body) ->
                  acc ^-^ !^"|" ^^ pp_pattern pattern ^^ !^"=>" ^^ pp_term body
                  ^-^ newline)
                !^"" cases))
  | IfExpr (t, b1, b2) ->
      nest
        (!^"if" ^^ pp_term t ^^ !^"then" ^^ pp_term b1 ^^ !^"else" ^^ pp_term b2)
  | EqType (t1, t2, tp) ->
      nest (pp_term t1 ^^ !^"==" ^^ pp_term t2 ^^ !^":>" ^^ pp_term tp)
  | Refl (t, tp) -> nest (!^"refl" ^^ pp_term t ^^ !^":" ^^ pp_term tp)
  | Subst (nm, var, t1, t2, t3) ->
      nest
        (!^"subst" ^^ !^nm ^^ !^"("
        ^^ !^(Core.Var.to_string var)
        ^-^ !^"," ^^ pp_term t1 ^-^ !^"," ^^ pp_term t2 ^-^ !^"," ^^ pp_term t3
        ^-^ !^")")

let term_to_string (t : Core.term) : string = to_string 40 2 (pp_term t)

let print (term, tp) =
  print_endline
    (to_string 40 2
       (pp_term term ^-^ newline
       ^-^ nest (!^"\x1b[1mT:" ^^ pp_term tp ^-^ newline ^-^ !^"\x1b[0m")))

let pp_telescope (ts : Core.telescope) : SmartPrint.t =
  let rec aux acc = function
    | Core.Cons (nm, var, tp, ts) ->
        aux (acc ^-^ newline ^-^ !^nm ^^ !^(string_of_var var) ^^ pp_term tp) ts
    | Core.Empty -> acc
  in
  aux !^"" ts

let telescope_to_string (ts : Core.telescope) : string =
  to_string 40 2 (pp_telescope ts)

let rec pp_uterm ({ data = e; pos } : Raw.term) : SmartPrint.t =
  let parens_if_app ({ data; pos } as t : Raw.term) =
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
  | Case (t, var, tp, cases) ->
      let var_str =
        match var with Some nm -> !^" as " ^-^ !^nm | None -> !^""
      in
      let tp_str =
        match tp with Some tp -> !^" return" ^^ pp_uterm tp | None -> !^""
      in
      nest
        (!^"match" ^^ pp_uterm t ^^ var_str ^^ tp_str ^^ !^"with" ^-^ newline
        ^-^ nest
              (List.fold_left
                 (fun acc ((pattern : Raw.pattern), body) ->
                   acc ^-^ !^"|" ^^ pp_uTerm_pattern pattern ^^ !^"=>"
                   ^^ pp_uterm body ^-^ newline)
                 !^"" cases))
  | ADTSig (nm, ts) -> nest (!^"data" ^^ !^nm ^^ nest (pp_telescope ts))
  | ADTDecl (nm, ts, con_defs) ->
      nest
        (!^"data" ^^ !^nm
        ^^ nest
             (pp_telescope ts ^^ !^"=" ^-^ newline
             ^-^ nest
                   (List.fold_left
                      (fun acc (con_def : Raw.constructor_def) ->
                        nest
                          (!^"|" ^^ !^(con_def.cname)
                          ^^ pp_telescope con_def.telescope))
                      !^"" con_defs)))
  | IfExpr (t, b1, b2) ->
      nest
        (!^"if" ^^ pp_uterm t ^^ !^"then" ^^ pp_uterm b1 ^^ !^"else"
       ^^ pp_uterm b2)
  | EqType (t1, t2, tp) ->
      nest (pp_uterm t1 ^^ !^"==" ^^ pp_uterm t2 ^^ !^":>" ^^ pp_uterm tp)
  | Refl (t, tp) -> nest (!^"refl" ^^ pp_uterm t ^^ !^":" ^^ pp_uterm tp)
  | Subst (nm, t1, t2, t3) ->
      nest
        (!^"subst" ^^ !^nm ^^ !^"(" ^^ pp_uterm t1 ^-^ !^"," ^^ pp_uterm t2
       ^-^ !^"," ^^ pp_uterm t3 ^-^ !^")")

and pp_telescope (ts : Raw.telescope) : SmartPrint.t =
  match ts with
  | Empty -> !^""
  | Cons (x, t, (Cons (_, _, _) as ts)) ->
      parens (!^x ^-^ !^":" ^^ pp_uterm t) ^^ pp_telescope ts
  | Cons (x, t, Empty) -> parens (!^x ^-^ !^":" ^^ pp_uterm t)

let rec uterm_to_string (t : Raw.term) : string = to_string 40 2 (pp_uterm t)

let rec pp_whnf (e : Core.whnf) : SmartPrint.t =
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
  | Case (scrut, scrut_tp, var, tp, cases) ->
      let var_str =
        match var with
        | Some (nm, var) ->
            !^" as " ^-^ !^nm ^-^ !^"@" ^-^ !^(string_of_var var)
        | None -> !^""
      in
      let tp_str =
        match tp with Some tp -> !^" return" ^^ pp_term tp | None -> !^""
      in
      nest
        (!^"match" ^^ pp_whnf scrut ^-^ !^":" ^^ pp_term scrut_tp ^^ var_str
       ^^ tp_str ^^ !^"with" ^^ newline
        ^^ nest
             (List.fold_left
                (fun acc ((pattern : Core.pattern), body) ->
                  acc ^-^ !^"|" ^^ pp_pattern pattern ^^ !^"=>" ^^ pp_term body
                  ^-^ newline)
                !^"" cases))
  | IfExpr (t, b1, b2) ->
      nest
        (!^"if" ^^ pp_whnf t ^^ !^"then" ^^ pp_term b1 ^^ !^"else" ^^ pp_term b2)
  | EqType (t1, t2, tp) ->
      nest (pp_term t1 ^^ !^"==" ^^ pp_term t2 ^^ !^":>" ^^ pp_term tp)
  | Refl (t, tp) -> nest (!^"refl" ^^ pp_term t ^^ !^":" ^^ pp_term tp)
  | Subst (nm, var, t1, t2, t3) ->
      nest
        (!^"subst" ^^ !^nm ^^ !^"("
        ^^ !^(Core.Var.to_string var)
        ^-^ !^"," ^^ pp_term t1 ^-^ !^"," ^^ pp_whnf t2 ^-^ !^"," ^^ pp_term t3
        ^-^ !^")")

let rec whnf_to_string (t : Core.whnf) : string = to_string 40 2 (pp_whnf t)

let print_def ({ pos; data } : Raw.term) : unit =
  match data with
  | LetDef (nm, _)
  | LemmaDef (nm, _)
  | TermWithTypeAnno
      ( ( { pos = _; data = LetDef (nm, _) }
        | { pos = _; data = LemmaDef (nm, _) } ),
        _ ) ->
      print_endline ("\x1b[1m" ^ nm ^ "\x1b[0m")
  | _ -> print_endline "Expected definition at top level"

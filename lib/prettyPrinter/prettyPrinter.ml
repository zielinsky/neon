open TypeChecker

let rec term_to_string (t : term) : string =
  match t with
  | Type -> "Type"
  | Kind -> "Kind"
  | Var (nm, _) -> nm
  | Lambda (nm, _, tp_x, body) -> "(λ" ^ nm ^ ":" ^ (term_to_string tp_x) ^ " -> " ^ (term_to_string body) ^ ")"
  | Product (nm, _, tp_x, body) -> "(Π" ^ nm ^ ":" ^ (term_to_string tp_x) ^ " -> " ^ (term_to_string body) ^ ")"
  | App (t1, t2) -> "(" ^ (term_to_string t1) ^ ") (" ^ (term_to_string t2) ^ ")"

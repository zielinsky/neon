open UExpr

type var
type env
type term 

val infer_type : env -> UExpr.term -> term * term
val check_type : env -> UExpr.term -> term -> term 
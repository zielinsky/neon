type var
type env
type term 

val infer_type : env -> UserExpression.term -> term * term
val check_type : env -> UserExpression.term -> term -> term 
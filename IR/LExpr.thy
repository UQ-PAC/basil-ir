theory LExpr
  imports Expr
begin

section \<open>LExpr\<close>

text \<open>
Represent the left-hand side of assignments
in BASIL statements. The Scala implementation
actually uses a subtype of @{type expr} containing
only @{term Local} and @{term Register} to represent
this, but such subtyping is difficult to attain in
Isabelle with nice code extraction.

Instead, we create a new type to represent this
specific case and collapse this into the @{type expr}
constructors via code extraction.
\<close>

datatype lexpr =
  LRegister string nat
  | LLocal string type

subsection \<open>Translation Utilities\<close>

fun expr_of_lexpr
  where
    "expr_of_lexpr (LRegister n w) = Register n w"
  | "expr_of_lexpr (LLocal n t) = Local n t"

fun lexpr_of_expr
  where
    "lexpr_of_expr (Register n w) = LRegister n w"
  | "lexpr_of_expr (Local n t) = LLocal n t"
  | "lexpr_of_expr _ = undefined"

end


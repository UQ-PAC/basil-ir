theory Stmt
  imports LExpr
begin

section \<open>Immutable Statement\<close>

text \<open>
BASIL currently implements statements as mutable classes.
Such structures are difficult to model in Isabelle, so we first start
with an ADT capturing the same information.

Consider:
\<bullet> Making statements immutable in general
\<bullet> Moving MapStore into an expression
\<bullet> Collapsing Nop into a trivial Assert/Assume
\<close>

datatype stmt =
  Assign (lhs: lexpr) (rhs: expr) (lbl: label)
  | MapStore (mem: mem) (index: expr) (val: expr) (endian: endian) (size: nat) (lbl: label) 
  | Nop (lbl: label)
  | Assert (body: expr) (cmt: label) (lbl: label) 
  | Assume (body: expr) (cmt: label) (lbl: label) (sec: bool)

end
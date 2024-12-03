theory Value
  imports Main
begin

datatype primval =
  BoolVal bool
  | BitVecVal (val: int) (size: nat)
  | IntVal (val: int)
  | MemVal (mem: "int \<Rightarrow> primval") 

definition is_true
  where "is_true x \<equiv> x = (BoolVal True)"
definition is_false
  where "is_false x \<equiv> x = (BoolVal False)"

definition opt_is_true
  where "opt_is_true x \<equiv> case x of Some v \<Rightarrow> is_true v | _ \<Rightarrow> False"
definition opt_is_false
  where "opt_is_false x \<equiv> case x of Some v \<Rightarrow> is_false v | _ \<Rightarrow> False"



end
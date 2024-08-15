theory Smallint
  imports Main
begin

text \<open>
Quick hack for a representation of a signed 32-bit integer.
See @{theory HOL.Code_Numeral} for how to do this properly.
Plus should use a wrapped representation, rather than a subset,
to get semantics for addition, etc, for free.
Suspect there is one in the library somewhere already.
\<close>

typedef smallint = "{i :: int. -2147483648 \<le> i \<and> i < 2147483648}"
proof -
  have "0 < (2147483648 :: int)" by auto
  moreover have "(-2147483648 :: int) \<le> 0" by auto
  ultimately show ?thesis by blast
qed

setup_lifting type_definition_smallint


instantiation smallint :: equal
begin

lift_definition equal_smallint :: "smallint \<Rightarrow> smallint \<Rightarrow> bool"
  is "(=)" .

instance   
  apply standard
  apply transfer
  by simp
end 

instantiation smallint :: zero_neq_one
begin

lift_definition zero_smallint :: smallint
  is "0 :: int" by auto

declare zero_smallint.rep_eq [simp]

lift_definition one_smallint :: smallint
  is "1 :: int" by auto

declare one_smallint.rep_eq [simp]

instance   
  apply standard
  apply transfer
  by simp
end

code_printing
  type_constructor smallint \<rightharpoonup> (Scala) "Int"
  | constant Abs_smallint \<rightharpoonup> (Scala) "_"
  | constant "0 :: smallint" \<rightharpoonup> (Scala) "0"
  | constant "1 :: smallint" \<rightharpoonup> (Scala) "1"
  | constant "HOL.equal :: smallint \<Rightarrow> smallint \<Rightarrow> bool" \<rightharpoonup> (Scala) infixl 5 "=="

end
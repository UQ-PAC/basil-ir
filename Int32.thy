theory Int32
  imports Main HOL.Code_Numeral "HOL.String" "HOL-Library.Countable"
begin

(*
  Need a 'prelim' library:
    - BigInt, int32, string, boolean
    - List, Map
*)

fun forall
  where "forall (x#xs) f = (f x \<and> forall xs f)" | "forall [] f = True"

lemma forall_cong[fundef_cong]:
  assumes "xs = ys"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> f x = g x"
  shows "forall xs f = forall ys g"
  using assms(2) unfolding assms(1) by (induct ys) auto

code_printing
  constant "forall" \<rightharpoonup> (Scala) "_.forall_"

text \<open>
Quick hack for a representation of a signed 32-bit integer.
See @{theory HOL.Code_Numeral} for how to do this properly.
Plus should use a wrapped representation, rather than a subset,
to get semantics for addition, etc, for free.
Suspect there is one in the library somewhere already.
\<close>

typedef int32 = "{i :: int. -2147483648 \<le> i \<and> i < 2147483648}"
proof -
  have "0 < (2147483648 :: int)" by auto
  moreover have "(-2147483648 :: int) \<le> 0" by auto
  ultimately show ?thesis by blast
qed

setup_lifting type_definition_int32

instantiation int32 :: equal
begin

lift_definition equal_int32 :: "int32 \<Rightarrow> int32 \<Rightarrow> bool"
  is "(=)" .

instance   
  apply standard
  apply transfer
  by simp
end 

instantiation int32 :: zero_neq_one
begin

lift_definition zero_int32 :: int32
  is "0 :: int" by auto

declare zero_int32.rep_eq [simp]

lift_definition one_int32 :: int32
  is "1 :: int" by auto

declare one_int32.rep_eq [simp]

instance   
  apply standard
  apply transfer
  by simp
end

instantiation int32 :: order
begin

lift_definition less_eq_int32 ::  "int32 \<Rightarrow> int32 \<Rightarrow> bool"
  is "(\<le>)" .

lift_definition less_int32 ::  "int32 \<Rightarrow> int32 \<Rightarrow> bool"
  is "(<)" .

instance by standard (transfer; auto)+
end

instance int32 :: countable
proof 
  obtain to_nat where "inj (to_nat :: int \<Rightarrow> nat)"
    by blast
  moreover have "inj Rep_int32" 
    using Rep_int32_inject injI by metis
  ultimately show "\<exists>to_nat. inj (to_nat :: int32 \<Rightarrow> nat)"
    using inj_compose by auto
qed 

instance integer :: countable
proof 
  obtain to_nat where "inj (to_nat :: int \<Rightarrow> nat)"
    by blast
  moreover have "inj int_of_integer" 
    using int_of_integer_inject injI by metis
  ultimately show "\<exists>to_nat. inj (to_nat :: integer \<Rightarrow> nat)"
    using inj_compose by auto
qed 

code_printing
  type_constructor int32 \<rightharpoonup> (Scala) "Int"
  | constant "0 :: int32" \<rightharpoonup> (Scala) "0"
  | constant "1 :: int32" \<rightharpoonup> (Scala) "1"
  | constant "HOL.equal :: int32 \<Rightarrow> int32 \<Rightarrow> bool" \<rightharpoonup> (Scala) infixl 5 "=="
  | constant "less_eq :: int32 \<Rightarrow> int32 \<Rightarrow> bool" \<rightharpoonup> (Scala) infixl 5 "<="
  | constant "less :: int32 \<Rightarrow> int32 \<Rightarrow> bool" \<rightharpoonup> (Scala) infixl 5 "<"

end
theory Type
  imports Int32 Test
begin

section \<open>IRType\<close>

text \<open>Replication of IRType.\<close>
datatype type =
  BoolType
  | IntType
  | BVType (size: int32)
  | MapType (param: type) (result: type)

instance type :: countable
  by countable_datatype

subsection \<open>Export\<close>

code_printing
  type_constructor type \<rightharpoonup> (Scala) "IRType"
  | constant "BoolType" \<rightharpoonup> (Scala) "BoolType"
  | constant "BVType" \<rightharpoonup> (Scala) "BitVecType'(_)"
  | constant "MapType" \<rightharpoonup> (Scala) "MapType'(_,/ _)"
  | constant "IntType" \<rightharpoonup> (Scala) "IntType"

subsection \<open>Properties\<close>

text \<open>
Limit well-formed types such that:
\<bullet> Bitvector has positive width
\<bullet> Maps domains are limited to scalar types
\<close>
fun wf_type
  where
    "wf_type (BVType w) = (w > 0)"
  | "wf_type (MapType (MapType _ _) _) = False"
  | "wf_type (MapType t1 t2) = (wf_type t1 \<and> wf_type t2)"
  | "wf_type _ = True"


instantiation type :: count
begin

definition "to_int_type (x :: type) \<equiv> (1 :: integer)"

instance apply standard
  unfolding to_int_type_def
  apply auto
  done
end

end
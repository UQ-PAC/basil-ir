theory IRType
  imports Main Smallint
begin

text \<open>Replication of IRType\<close>
datatype IRType =
  BoolType
  | BitVecType (size: smallint)
  | IntType
  | MapType (param: IRType) (result: IRType)

text \<open>Link the above with Scala constructors. There is some issue with introducing parentheses on constructor arguments.\<close>
code_printing
    type_constructor IRType \<rightharpoonup> (Scala) "IRType"
  | constant "BoolType" \<rightharpoonup> (Scala) "BoolType"
  | constant "BitVecType" \<rightharpoonup> (Scala) "BitVecType/(_/)"
  | constant "MapType" \<rightharpoonup> (Scala) "MapType/(_,/ _/)"
  | constant "IntType" \<rightharpoonup> (Scala) "IntType"

text \<open>Illustration of a partial function & deconstructors, converting a type to its width.\<close>
fun width_of_type
  where
    "width_of_type (BoolType) = 1"
  | "width_of_type (BitVecType w) = w"
  | "width_of_type _ = undefined"

text \<open>Illustration of constructors, along with basic tests of @{type smallint}}\<close>
fun from_width
  where
    "from_width n = (if n = 0 then undefined
                     else if n = 1 then BoolType
                     else BitVecType n)"

export_code width_of_type from_width in Scala module_name IRTypeHelpers file_prefix "test/IRType"

end
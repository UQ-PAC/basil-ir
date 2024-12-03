theory Type
  imports Main
begin

section \<open>IRType\<close>

text \<open>Replication of IRType.\<close>
datatype type =
  BoolType
  | IntType
  | BVType (size: nat)
  | MapType (param: type) (result: type)

end
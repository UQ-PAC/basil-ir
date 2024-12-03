theory Expr
  imports Type Enums
begin

section \<open>Memory\<close>

text \<open>Replication of Variables. All variable references seem to carry their type.\<close>
datatype mem =
  StackMem (name: string) (domain_width: nat) (range_width: nat)
  | SharedMem (name: string) (domain_width: nat) (range_width: nat)

subsection \<open>Type Checking\<close>

fun type_of_mem
  where
    "type_of_mem (StackMem _ k v) = MapType (BVType k) (BVType v)"
  | "type_of_mem (SharedMem _ k v) = MapType (BVType k) (BVType v)"

section \<open>Expressions\<close>

datatype expr =
    TrueLit 
  | FalseLit
  | IntLit int
  | BVLit int nat
  | Register string nat
  | Local string type
  | BVExtract nat nat expr
  | BVRepeat nat expr
  | BVZExt nat expr
  | BVSExt nat expr
  | Uop unop expr
  | Bop binop expr expr
  | FnCall string "expr list" type 
  | MapLoad mem expr endian nat

end
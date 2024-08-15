theory Value
  imports IRType
begin

datatype primval =
  BoolVal bool
  | BitVecVal (val: nat) (size: smallint)

datatype val =
  Prim primval
  | MapVal (fn: "primval \<rightharpoonup> val")

fun instance_of
  where
    "instance_of (Prim (BoolVal _)) BoolType = True"
  | "instance_of (Prim (BitVecVal _ s)) (BitVecType s') = (s = s')"
  | "instance_of (MapVal f) (MapType _ _) = True"
  | "instance_of _ _ = False"

fun instances_of
  where
    "instances_of ((x,t)#xs) ((y,v)#ys) = (x = y \<and> instance_of v t \<and> instances_of xs ys)"
  | "instances_of [] [] = True"
  | "instances_of _ _ = False"

end
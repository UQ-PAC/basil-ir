theory Expr
  imports Type Enums
begin

section \<open>Memory\<close>

text \<open>Replication of Variables. All variable references seem to carry their type.\<close>
datatype mem =
  StackMem string int32 int32
  | SharedMem string int32 int32

instance mem :: countable
  by countable_datatype

code_printing
  type_constructor mem \<rightharpoonup> (Scala) "Memory"
  | constant "StackMem" \<rightharpoonup> (Scala) "StackMemory'(_,/ _,/ _)"
  | constant "SharedMem" \<rightharpoonup> (Scala) "SharedMemory'(_,/ _,/ _)"

subsection \<open>Type Checking\<close>

fun type_of_mem
  where
    "type_of_mem (StackMem _ k v) = MapType (BVType k) (BVType v)"
  | "type_of_mem (SharedMem _ k v) = MapType (BVType k) (BVType v)"

section \<open>Expressions\<close>

datatype expr =
    TrueLit 
  | FalseLit
  | IntLit integer
  | BVLit integer int32
  | Register string int32
  | Local string type
  | BVExtract int32 int32 expr
  | BVRepeat int32 expr
  | BVZExt int32 expr
  | BVSExt int32 expr
  | Uop unop expr
  | Bop binop expr expr
  | FnCall string "expr list" type 
  | MapLoad mem expr endian int32

instance expr :: countable
  by countable_datatype

code_printing
  type_constructor expr \<rightharpoonup> (Scala) "Expr"
  | constant "TrueLit" \<rightharpoonup> (Scala) "TrueLiteral"
  | constant "FalseLit" \<rightharpoonup> (Scala) "FalseLiteral"
  | constant "IntLit" \<rightharpoonup> (Scala) "IntLiteral'(_)"
  | constant "BVLit" \<rightharpoonup> (Scala) "BitVecLiteral'(_,/ _)"
  | constant "Register" \<rightharpoonup> (Scala) "Register'(_,/ _)"
  | constant "Local" \<rightharpoonup> (Scala) "LocalVar'(_,/ _)"
  | constant "BVExtract" \<rightharpoonup> (Scala) "Extract'(_,/ _,/ _)"
  | constant "BVRepeat" \<rightharpoonup> (Scala) "Repeat'(_,/ _)"
  | constant "BVZExt" \<rightharpoonup> (Scala) "ZeroExtend'(_,/ _)"
  | constant "BVSExt" \<rightharpoonup> (Scala) "SignExtend'(_,/ _)"
  | constant "Uop" \<rightharpoonup> (Scala) "UnaryExpr'(_,/ _)"
  | constant "Bop" \<rightharpoonup> (Scala) "BinaryExpr'(_,/ _,/ _)"
  | constant "FnCall" \<rightharpoonup> (Scala) "UninterpretedFunction'(_,/ _,/ _)"
  | constant "MapLoad" \<rightharpoonup> (Scala) "MemoryLoad'(_,/ _,/ _,/ _)"

fun wf_expr
  where
    "wf_expr (BVLit _ w) = (w > 0)"
  | "wf_expr (Local _ t) = wf_type t"
  | "wf_expr (Register _ w) = wf_type (BVType w)"
  | "wf_expr (BVExtract hi lo e) = (hi \<ge> lo \<and> lo \<ge> 0 \<and> wf_expr e)" (* TODO: type of e *)
  | "wf_expr (BVRepeat rep e) = (rep > 0 \<and> wf_expr e)"
  | "wf_expr (BVZExt w e) = (w > 0 \<and> wf_expr e)"
  | "wf_expr (BVSExt w e) = (w > 0 \<and> wf_expr e)"
  | "wf_expr (Uop f e) = wf_expr e"
  | "wf_expr (Bop f l r) = (wf_expr l \<and> wf_expr r)"
  | "wf_expr (FnCall _ es t) = (forall es wf_expr \<and> wf_type t)"
  | "wf_expr (MapLoad _ e _ s) = (s > 0 \<and> wf_expr e)"
  | "wf_expr _ = True"

fun type_of_expr
  where
    "type_of_expr (TrueLit) = BoolType"
  | "type_of_expr (FalseLit) = BoolType"
  | "type_of_expr (BVLit _ w) = BVType w"
  | "type_of_expr (IntLit _) = IntType"
  | "type_of_expr (Register _ w) = BVType w"
  | "type_of_expr (Local _ t) = t"
  | "type_of_expr _ = undefined"


instantiation expr :: count
begin

definition "to_int_expr (x :: expr) \<equiv>  (1 :: integer)"

instance apply standard
  unfolding to_int_expr_def
  apply auto
  done
end

fun get_int :: "'a::count \<Rightarrow> integer"
  where "get_int t = to_int t * 2"

fun use_case :: "type \<Rightarrow> expr \<Rightarrow> integer"
  where "use_case t e = get_int t + get_int e"

export_code use_case to_int in Scala

end
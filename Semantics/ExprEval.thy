theory ExprEval
  imports Value "../IR/Expr"
begin

subsection \<open>Bitvector Operations\<close>

definition prim_asr :: "int \<Rightarrow> nat \<Rightarrow> int"
  where "prim_asr v n \<equiv> drop_bit n v"

definition prim_lsl :: "int \<Rightarrow> nat \<Rightarrow> int"
  where "prim_lsl v n \<equiv> push_bit n v"

definition mask_bits :: "int \<Rightarrow> nat \<Rightarrow> int"
  where "mask_bits v n \<equiv> and v (mask n)"

fun prim_extract
  where 
    "prim_extract hi lo (BitVecVal v w) = (
      if hi \<le> lo \<or> lo < 0 \<or> lo > w then None else
      let w' = hi - lo in
      Some (BitVecVal (mask_bits (prim_asr v lo) w') w'))"
  | "prim_extract _ _ _ = None"

value "prim_extract 2 0 (BitVecVal 7 32)"
value "prim_extract 2 0 (BitVecVal 8 32)"
value "prim_extract 2 1 (BitVecVal 7 32)"
value "prim_extract 2 2 (BitVecVal 7 32)"
value "prim_extract 2 2 (BitVecVal 7 32)"

function list_init
  where "list_init (n :: nat) =
          (if n \<le> 0 then [] else (n - 1)#(list_init (n - 1)))"
  by auto
termination
  sorry

fun prim_repeat
  where 
    "prim_repeat n (BitVecVal v w) = (
      let l = list_init n in
      let bv = foldl (\<lambda>acc n. or acc (prim_lsl v (n * w))) 0 l in
      Some (BitVecVal bv (n * w)))"
  | "prim_repeat _ _ = None"

value "prim_repeat 3 (BitVecVal 1 4)"

fun prim_zext
  where 
    "prim_zext n (BitVecVal v w) = (if n < 0 then None else Some (BitVecVal v (w + n)))"
  | "prim_zext _ _ = None"

fun prim_uop
  where
    "prim_uop BoolNOT (BoolVal b)   = Some (BoolVal (\<not> b))"
  | "prim_uop BoolNOT _ = None"
  | "prim_uop IntNEG (IntVal i)     = Some (IntVal (- i))" 
  | "prim_uop IntNEG  _ = None"
  | "prim_uop BVNOT (BitVecVal v w) = Some (BitVecVal (not v) w)"
  | "prim_uop BVNOT  _ = None" 
  | "prim_uop BVNEG (BitVecVal v w) = Some (BitVecVal (mask_bits (- v) w) w)" 
  | "prim_uop BVNEG _ = None"

fun bool_op
  where 
    "bool_op f (BoolVal a) (BoolVal b) = Some (BoolVal (f a b))" 
  | "bool_op _ _ _ = None"

fun bv_op_simp
  where 
    "bv_op_simp f (BitVecVal a w) (BitVecVal b w') = (if w = w' then Some (BitVecVal (f a b) w) else None)" 
  | "bv_op_simp _ _ _ = None"

fun prim_concat
  where
    "prim_concat (BitVecVal a w) (BitVecVal b w') = Some (BitVecVal (prim_lsl a w' + b) (w + w'))"
  | "prim_concat _ _ = None"

fun concat_bvs_rec :: "(int \<times> nat) list \<Rightarrow> (int \<times> nat)"
  where
    "concat_bvs_rec [(v,w)] = (v,w)"
  | "concat_bvs_rec ((v,w)#xs) = (
      let (a :: int \<times> nat) = concat_bvs_rec xs in
      let (v'' :: int) = prim_lsl v (snd a) in
      let (m :: int) = or (fst a) v'' in
      ((m, w + (snd a))))"
  | "concat_bvs_rec _ = undefined"

fun prim_bop
  where
    "prim_bop BoolEQ       = bool_op (=)"
  | "prim_bop BoolNEQ      = bool_op (\<noteq>)"
  | "prim_bop BoolAND      = bool_op (\<and>)"
  | "prim_bop BoolOR       = bool_op (\<or>)"
  | "prim_bop BoolIMPLIES  = bool_op (\<longrightarrow>)"
  | "prim_bop BoolEQUIV    = bool_op (=)"

  | "prim_bop BVAND    = bv_op_simp (and)"
  | "prim_bop BVOR     = bv_op_simp (or)"
  | "prim_bop BVXOR    = bv_op_simp (xor)"
  | "prim_bop BVADD    = bv_op_simp (+)"
  | "prim_bop BVMUL    = bv_op_simp (*)"
  | "prim_bop BVSUB    = bv_op_simp (-)"

  | "prim_bop BVNAND   = bv_op_simp (\<lambda>a b. not (and a b))"
  | "prim_bop BVNOR    = bv_op_simp (\<lambda>a b. not (or a b))"
  | "prim_bop BVXNOR   = bv_op_simp (\<lambda>a b. not (xor a b))"

  | "prim_bop BVCONCAT = prim_concat"

  | "prim_bop _  = (\<lambda>a b. None)"



(*
  
  | BVUDIV
  | BVUREM
  | BVSDIV 
  | BVSREM 
  | BVSMOD 

  | BVASHR 
  | BVSHL
  | BVLSHR 

  | BVULT  
  | BVCOMP 
  | BVULE  
  | BVUGT  
  | BVUGE  
  | BVSLT  
  | BVSLE  
  | BVSGT
  | BVSGE  
  | BVEQ   
  | BVNEQ  

  | IntADD 
  | IntMUL 
  | IntSUB 
  | IntDIV 
  | IntMOD 
  | IntEQ  
  | IntNEQ 
  | IntLT  
  | IntLE  
  | IntGT  
  | IntGE  *)

record EvalState =
  registers :: "string \<rightharpoonup> primval"
  locals :: "string \<rightharpoonup> primval"
  mems :: "string \<rightharpoonup> primval"
  fns :: "string \<Rightarrow> primval list \<Rightarrow> primval option"

definition bind_option :: "'a option \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> 'b option"
  where "bind_option a f \<equiv> case a of Some v \<Rightarrow> f v | _ \<Rightarrow> None"

fun eval_expr
  where
    "eval_expr _ (TrueLit)   = Some (BoolVal True)"
  | "eval_expr _ (FalseLit)  = Some (BoolVal False)"
  | "eval_expr _ (IntLit i)  = Some (IntVal i)"
  | "eval_expr _ (BVLit i w) = Some (BitVecVal i w)"

  | "eval_expr \<sigma> (Register n w) = (registers \<sigma> n)"
  | "eval_expr \<sigma> (Local n t) =  (locals \<sigma> n)"

  | "eval_expr \<sigma> (BVExtract hi lo e) =
      bind_option (eval_expr \<sigma> e) (prim_extract hi lo)"
  | "eval_expr \<sigma> (BVRepeat reps e) =
      bind_option (eval_expr \<sigma> e) (prim_repeat reps)"
  | "eval_expr \<sigma> (BVZExt w e) =
      bind_option (eval_expr \<sigma> e) (prim_zext w)"

  | "eval_expr \<sigma> (Uop op e) =
      bind_option (eval_expr \<sigma> e) (prim_uop op)"
  | "eval_expr \<sigma> (Bop op e1 e2) =
      bind_option (eval_expr \<sigma> e1) (\<lambda>v1.
        bind_option (eval_expr \<sigma> e2) (prim_bop op v1))"

end
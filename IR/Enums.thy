theory Enums
  imports Main
begin

section \<open>Enums\<close>

text \<open>
Collection of enums used throughout the IR. Notes:
\<bullet> This file may take some time due to the size of the enums.
\<bullet> Not all of these operations are necessary, a lot of redundancy.
\<bullet> It may be worthwhile breaking these down into various subtypes, as done in Scala.
\<bullet> Not sure if these have to be enums, could fold other operations given nat args.
\<close>

subsection \<open>Endian\<close>

datatype endian =
  BigEndian
  | LittleEndian

subsection \<open>UnOp\<close>

datatype unop =
  BoolNOT 
  | IntNEG 
  | BVNOT 
  | BVNEG 

subsection \<open>BinOp\<close>

datatype binop =
  BoolEQ
  | BoolNEQ
  | BoolAND
  | BoolOR
  | BoolIMPLIES
  | BoolEQUIV
  | BVAND  
  | BVOR   
  | BVADD  
  | BVMUL  
  | BVUDIV 
  | BVUREM 
  | BVSHL  
  | BVLSHR 
  | BVULT  
  | BVNAND 
  | BVNOR  
  | BVXOR  
  | BVXNOR 
  | BVCOMP 
  | BVSUB  
  | BVSDIV 
  | BVSREM 
  | BVSMOD 
  | BVASHR 
  | BVULE  
  | BVUGT  
  | BVUGE  
  | BVSLT  
  | BVSLE  
  | BVSGT  
  | BVSGE  
  | BVEQ   
  | BVNEQ  
  | BVCONCAT
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
  | IntGE  

section \<open>Labels\<close>

type_synonym label = "string option"

end
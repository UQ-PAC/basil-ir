theory Enums
  imports Int32
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

instance endian :: countable
  by countable_datatype

code_printing
  type_constructor endian \<rightharpoonup> (Scala) "Endian"
  | constant "BigEndian"    \<rightharpoonup> (Scala) "BigEndian"
  | constant "LittleEndian" \<rightharpoonup> (Scala) "LittleEndian"

subsection \<open>UnOp\<close>

datatype unop =
  BoolNOT 
  | IntNEG 
  | BVNOT 
  | BVNEG 

instance unop :: countable
  by countable_datatype

code_printing
  type_constructor unop \<rightharpoonup> (Scala) "UnOp"
  | constant "BoolNOT" \<rightharpoonup> (Scala) "BoolNOT"
  | constant "IntNEG"  \<rightharpoonup> (Scala) "IntNEG"
  | constant "BVNOT"   \<rightharpoonup> (Scala) "BVNOT"
  | constant "BVNEG"   \<rightharpoonup> (Scala) "BVNEG"

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

instance binop :: countable
  by countable_datatype

code_printing
  type_constructor binop \<rightharpoonup> (Scala) "BinOp"
  | constant "BoolEQ"      \<rightharpoonup> (Scala) "BoolEQ"     
  | constant "BoolNEQ"     \<rightharpoonup> (Scala) "BoolNEQ"    
  | constant "BoolAND"     \<rightharpoonup> (Scala) "BoolAND"    
  | constant "BoolOR"      \<rightharpoonup> (Scala) "BoolOR"     
  | constant "BoolIMPLIES" \<rightharpoonup> (Scala) "BoolIMPLIES"
  | constant "BoolEQUIV"   \<rightharpoonup> (Scala) "BoolEQUIV"  
  | constant "BVAND"       \<rightharpoonup> (Scala) "BVAND"      
  | constant "BVOR"        \<rightharpoonup> (Scala) "BVOR"       
  | constant "BVADD"       \<rightharpoonup> (Scala) "BVADD"      
  | constant "BVMUL"       \<rightharpoonup> (Scala) "BVMUL"      
  | constant "BVUDIV"      \<rightharpoonup> (Scala) "BVUDIV"     
  | constant "BVUREM"      \<rightharpoonup> (Scala) "BVUREM"     
  | constant "BVSHL"       \<rightharpoonup> (Scala) "BVSHL"      
  | constant "BVLSHR"      \<rightharpoonup> (Scala) "BVLSHR"     
  | constant "BVULT"       \<rightharpoonup> (Scala) "BVULT"      
  | constant "BVNAND"      \<rightharpoonup> (Scala) "BVNAND"     
  | constant "BVNOR"       \<rightharpoonup> (Scala) "BVNOR"      
  | constant "BVXOR"       \<rightharpoonup> (Scala) "BVXOR"      
  | constant "BVXNOR"      \<rightharpoonup> (Scala) "BVXNOR"     
  | constant "BVCOMP"      \<rightharpoonup> (Scala) "BVCOMP"     
  | constant "BVSUB"       \<rightharpoonup> (Scala) "BVSUB"      
  | constant "BVSDIV"      \<rightharpoonup> (Scala) "BVSDIV"     
  | constant "BVSREM"      \<rightharpoonup> (Scala) "BVSREM"     
  | constant "BVSMOD"      \<rightharpoonup> (Scala) "BVSMOD"     
  | constant "BVASHR"      \<rightharpoonup> (Scala) "BVASHR"     
  | constant "BVULE"       \<rightharpoonup> (Scala) "BVULE"      
  | constant "BVUGT"       \<rightharpoonup> (Scala) "BVUGT"      
  | constant "BVUGE"       \<rightharpoonup> (Scala) "BVUGE"      
  | constant "BVSLT"       \<rightharpoonup> (Scala) "BVSLT"      
  | constant "BVSLE"       \<rightharpoonup> (Scala) "BVSLE"      
  | constant "BVSGT"       \<rightharpoonup> (Scala) "BVSGT"      
  | constant "BVSGE"       \<rightharpoonup> (Scala) "BVSGE"      
  | constant "BVEQ"        \<rightharpoonup> (Scala) "BVEQ"       
  | constant "BVNEQ"       \<rightharpoonup> (Scala) "BVNEQ"      
  | constant "BVCONCAT"    \<rightharpoonup> (Scala) "BVCONCAT"   
  | constant "IntADD"      \<rightharpoonup> (Scala) "IntADD"     
  | constant "IntMUL"      \<rightharpoonup> (Scala) "IntMUL"     
  | constant "IntSUB"      \<rightharpoonup> (Scala) "IntSUB"     
  | constant "IntDIV"      \<rightharpoonup> (Scala) "IntDIV"     
  | constant "IntMOD"      \<rightharpoonup> (Scala) "IntMOD"     
  | constant "IntEQ"       \<rightharpoonup> (Scala) "IntEQ"      
  | constant "IntNEQ"      \<rightharpoonup> (Scala) "IntNEQ"     
  | constant "IntLT"       \<rightharpoonup> (Scala) "IntLT"      
  | constant "IntLE"       \<rightharpoonup> (Scala) "IntLE"      
  | constant "IntGT"       \<rightharpoonup> (Scala) "IntGT"      
  | constant "IntGE"       \<rightharpoonup> (Scala) "IntGE"      

end
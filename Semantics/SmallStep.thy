theory SmallStep
  imports "../IR/Procedure" ExprEval
begin

text \<open>Convenience structure, represent current program structure\<close>
datatype AbstractProgram =
  CurBlock "stmt list" "jump" |
  Failure |
  Magic

record ProgramState = EvalState +
  cur_proc :: "proc"

inductive small_step
  where
    "\<lbrakk> s = Assign (LRegister reg _) e _ ;
       \<sigma>' = \<sigma>\<lparr> registers := ((registers \<sigma>)(reg := eval_expr \<sigma> e))\<rparr>\<rbrakk> \<Longrightarrow> 
      small_step (CurBlock (s#rs) j) \<sigma> (CurBlock rs j) \<sigma>'" |

    (* Assert *)
    "\<lbrakk>  s = Assert e _ _ ; opt_is_true (eval_expr \<sigma> e) \<rbrakk> \<Longrightarrow>
      small_step (CurBlock (s#rs) j) \<sigma> (CurBlock rs j) \<sigma>" |
    "\<lbrakk> s = (Assert e _ _) ; opt_is_false (eval_expr \<sigma> e) \<rbrakk> \<Longrightarrow> 
      small_step (CurBlock (s#rs) j) \<sigma> Failure \<sigma>" |

    (* Assume *)
    "\<lbrakk> s = (Assume e _ _ _) ; opt_is_true (eval_expr \<sigma> e) \<rbrakk> \<Longrightarrow> 
      small_step (CurBlock (s#rs) j) \<sigma> (CurBlock rs j) \<sigma>" |
    "\<lbrakk> s = (Assume e _ _ _) ; opt_is_false (eval_expr \<sigma> e) \<rbrakk> \<Longrightarrow> 
      small_step (CurBlock (s#rs) j) \<sigma> Magic \<sigma>" 

end
theory Stmt
  imports LExpr Expr HOL.Option   
    "HOL-Imperative_HOL.Imperative_HOL"

begin

type_synonym label = "string option"

section \<open>Immutable Statement\<close>

(*
Consider collapsing this to a record with a type field.
*)

datatype istmt =
  Assign (lhs: lexpr) (rhs: expr) (lbl: label)
  | MapStore (mem: mem) (index: expr) (val: expr) (endian: endian) (size: int32) (lbl: label) 
  | Nop (lbl: label)
  | Assert (body: expr) (cmt: label) (lbl: label) 
  | Assume (body: expr) (cmt: label) (lbl: label) (chkSec: bool)

fun ulhs
  where 
    "ulhs f (Assign l r s) = (Assign (f l) r s)"
  | "ulhs f _ = undefined"

fun urhs
  where 
    "urhs f (Assign l r s) = (Assign l (f r) s)"
  | "urhs f _ = undefined"

fun ulbl
  where 
    "ulbl f (Assign l r s) = (Assign l r (f s))"
  | "ulbl f (MapStore m i v e w s) = (MapStore m i v e w (f s))"
  | "ulbl f _ = undefined"


instance istmt :: countable
  by countable_datatype

instance istmt :: heap ..

code_printing
  type_constructor istmt \<rightharpoonup> (Scala) "Statement"
  | constant "Assign"   \<rightharpoonup> (Scala) "Assign'(_,/ _,/ _)"
  | constant "MapStore" \<rightharpoonup> (Scala) "MemoryAssign'(_,/ _,/ _,/ _,/ _,/ _)"
  | constant "Nop"      \<rightharpoonup> (Scala) "NOP'(_)"
  | constant "Assert"   \<rightharpoonup> (Scala) "Assert'(_,/ _,/ _)"
  | constant "Assume"   \<rightharpoonup> (Scala) "Assume'(_,/ _,/ _,/ _)"

fun wf_istmt
  where
    "wf_istmt (Assign x e _) = (wf_expr e)"
  | "wf_istmt (MapStore m i v _ w _) = (w > 0 \<and> wf_expr i \<and> wf_expr v)"
  | "wf_istmt (Nop _) = True"
  | "wf_istmt (Assert e _ _) = (wf_expr e)"
  | "wf_istmt (Assume e _ _ _) = (wf_expr e)"

section \<open>Mutable Statement\<close>

type_synonym stmt = "istmt ref"

definition get_stmt :: "stmt \<Rightarrow> istmt Heap"
  where "get_stmt \<equiv> Ref.lookup"

definition set_stmt :: "stmt \<Rightarrow> istmt \<Rightarrow> unit Heap"
  where "set_stmt \<equiv> Ref.update"

definition get_stmt_field :: "(istmt \<Rightarrow> 'a) \<Rightarrow> stmt \<Rightarrow> 'a Heap"
  where "get_stmt_field f s \<equiv> do {
            cur \<leftarrow> get_stmt s;
            return (f cur)
          }"

definition upd_stmt :: "(istmt \<Rightarrow> istmt) \<Rightarrow> stmt \<Rightarrow> unit Heap"
  where "upd_stmt f s \<equiv> do {
            cur \<leftarrow> get_stmt s;
            set_stmt s (f cur)
          }"

subsection \<open>Interface\<close>

definition get_lhs :: "stmt \<Rightarrow> lexpr Heap"
  where "get_lhs \<equiv> get_stmt_field lhs"
definition upd_lhs :: "stmt \<Rightarrow> lexpr \<Rightarrow> unit Heap"
  where "upd_lhs s l \<equiv> upd_stmt (ulhs (\<lambda>_. l)) s"

definition get_rhs :: "stmt \<Rightarrow> expr Heap"
  where "get_rhs \<equiv> get_stmt_field rhs"
definition upd_rhs :: "stmt \<Rightarrow> expr \<Rightarrow> unit Heap"
  where "upd_rhs s l \<equiv> upd_stmt (urhs (\<lambda>_. l)) s"

definition isAssign
  where "isAssign s \<equiv>  (get_stmt s \<bind> (return o is_Assign))"
definition isMapStore
  where "isMapStore s \<equiv>  (get_stmt s \<bind> (return o is_MapStore))"
definition isNop
  where "isNop s \<equiv>  (get_stmt s \<bind> (return o is_Nop))"
definition isAssume
  where "isAssume s \<equiv>  (get_stmt s \<bind> (return o is_Assume))"
definition isAssert
  where "isAssert s \<equiv>  (get_stmt s \<bind> (return o is_Assert))"

(*
  We need to generate a structure that casts via pattern match and then applies
  appropriate access methods.

  - Put the type into the pointer, gives you something immediate to match on.
  - Somehow make the function definition work with loads.
*)

record Test =
  Var :: "lexpr"

fun test_upd
  where "test_upd v = v\<lparr> Var := LRegister (String.explode (STR ''asd'')) 0 \<rparr>"

export_code test_upd in Scala

definition custom_cases
  where "custom_cases p assign map \<equiv> do {
    b \<leftarrow> isAssign p1;

    }"

code_printing
  constant "get_lhs" \<rightharpoonup> (Scala) "_.lhs"
  | constant "get_rhs" \<rightharpoonup> (Scala) "_.rhs"
  | constant "isAssign" \<rightharpoonup> (Scala) "_ : Assign"

definition wf_stmt
  where "wf_stmt p1 \<equiv> do {
          b \<leftarrow> isAssign p1;
          if b then do {
            e \<leftarrow> get_rhs p1;
            return (wf_expr e)
          } else do {
            return True
          }
        }"

setup \<open>

let

open Code_Thingol;

val pretty_term = Syntax.pretty_term
val pwriteln = Pretty.writeln

fun pp_optname v = case v of
    NONE => "None"
  | SOME a => a

fun pp_iterm t = case t of
    IConst c => "IConst"
  | IVar a => "IVar " ^ pp_optname a
  | a `$ b => "(" ^ pp_iterm a ^ ") `$ (" ^ pp_iterm b ^ ")"
  | (n,_) `|=> (t,_) => "(" ^ pp_optname n ^ ")`|\<Rightarrow>(" ^ pp_iterm t ^ ")" 
  | ICase {term = t, ... } => "ICase(" ^ pp_iterm t ^ ")"

val imp_program =
  let
    val is_bind = curry (=) \<^const_name>\<open>bind\<close>;
    val is_return = curry (=) \<^const_name>\<open>return\<close>;
    val dummy_name = "";
    val dummy_case_term = IVar NONE;
    (*assumption: dummy values are not relevant for serialization*)
    val unitT = \<^type_name>\<open>unit\<close> `%% [];
    val unitt =
      IConst { sym = Code_Symbol.Constant \<^const_name>\<open>Unity\<close>, typargs = [], dicts = [], dom = [],
        annotation = NONE, range = unitT };

    fun dest_abs ((v, ty) `|=> (t, _), _) = ((v, ty), t)
      | dest_abs (t, ty) =
          let
            val vs = fold_varnames cons t [];
            val v = singleton (Name.variant_list vs) "x";
            val ty' = (hd o fst o unfold_fun) ty;
          in ((SOME v, ty'), t `$ IVar (SOME v)) end;

    fun force (t as IConst { sym = Code_Symbol.Constant c, ... } `$ t') = if is_return c
          then t' else t `$ unitt
      | force t = t `$ unitt;

    (* Seems to be setting up a definition? *)
    fun tr_bind'' [(t1, _), (t2, ty2)] =
      let
        val ((v, ty), t) = dest_abs (t2, ty2);
        val _ = writeln (pp_iterm t1);
        val _ = writeln (pp_iterm t2);
        val _ = writeln (pp_iterm t);
      in ICase { term = force t1, typ = ty, 
                 clauses = [(IVar v, tr_bind' t)], primitive = dummy_case_term } end

    and tr_bind' t = case unfold_app t
     of (IConst { sym = Code_Symbol.Constant c, dom = ty1 :: ty2 :: _, ... }, [x1, x2]) => if is_bind c
          then tr_bind'' [(x1, ty1), (x2, ty2)]
          else force t
      | _ => force t;

    fun imp_monad_bind'' ts = (SOME dummy_name, unitT) `|=>
      (ICase { term = IVar (SOME dummy_name), typ = unitT, 
               clauses = [(unitt, tr_bind'' ts)], primitive = dummy_case_term }, unitT)

    fun imp_monad_bind' (const as { sym = Code_Symbol.Constant c, dom = dom, ... }) ts = 
       if is_bind c then case (ts, dom)
       of ([t1, t2], ty1 :: ty2 :: _) => imp_monad_bind'' [(t1, ty1), (t2, ty2)]
        | ([t1, t2, t3], ty1 :: ty2 :: _) => imp_monad_bind'' [(t1, ty1), (t2, ty2)] `$ t3
        | (ts, _) => imp_monad_bind (saturated_application 2 (const, ts))
      else IConst const `$$ map imp_monad_bind ts

    and imp_monad_bind (IConst const) = imp_monad_bind' const []
      | imp_monad_bind (t as IVar _) = t
      | imp_monad_bind (t as _ `$ _) = (case unfold_app t
         of (IConst const, ts) => imp_monad_bind' const ts
          | (t, ts) => imp_monad_bind t `$$ map imp_monad_bind ts)
      | imp_monad_bind (v_ty `|=> t) = v_ty `|=> apfst imp_monad_bind t
      | imp_monad_bind (ICase { term = t, typ = ty, clauses = clauses, primitive = t0 }) =
          ICase { term = imp_monad_bind t, typ = ty,
            clauses = (map o apply2) imp_monad_bind clauses, primitive = imp_monad_bind t0 };

  in (Code_Symbol.Graph.map o K o map_terms_stmt) imp_monad_bind end;

in

Code_Target.add_derived_target ("Scala_imp2", [("Scala", imp_program)])

end

\<close>


(*
record state =
  Stmts :: "stmt \<Rightarrow> istmt"

type_synonym 'a stm = "state \<Rightarrow> 'a \<times> state"

definition bind :: "'a stm \<Rightarrow> ('a \<Rightarrow> 'b stm) \<Rightarrow> 'b stm"
  where "bind a f \<equiv> \<lambda>st. let (a,st') = a st in f a st'"

definition return :: "'a \<Rightarrow> 'a stm"
  where "return a \<equiv> \<lambda>st. (a,st)"

adhoc_overloading
  Monad_Syntax.bind bind

definition get_stmt :: "stmt \<Rightarrow> istmt stm"
  where "get_stmt s \<equiv> \<lambda>st. (Stmts st s,st)"

definition wf_stmt
  where "wf_stmt p1 p2 \<equiv> do {
          s1 \<leftarrow> get_stmt p1;
          s2 \<leftarrow> get_stmt p2;
          return (wf_istmt s1)
        }"
*)
export_code wf_stmt in Scala_imp2

(*
wf_stmt is lookup, apply above.
Alt is a series of helpers that internally lookup?


isAssign (stmt) st = bool * st
...

run the wf function over the entire list?
  - 

*)


(*
  Statements are mutable, only equal under some pointer notion.
  You'd have to model this here.
  But it would be a whole lot nicer if you can just get this by
  refinement.

  Destructor:
    \<bullet> Just use this else setup, its annoying but it works
    \<bullet> Could get some extra assistance to move the Else last
  Fancy Destructor:
    \<bullet> Convert LHS to placeholder, maintain nested
    \<bullet> Need to print as 'x : Type \<Rightarrow> match (x.field1,x.field2,...) with { Pat \<Rightarrow> ... }'
  Equality:
    \<bullet> Just use structural equality
  Mutability:
    \<bullet> Generated code will never leverage mutability
    \<bullet> But we will need some way to reason over Scala code that leverages
      mutability
*)

(*
These structures have to be finite, can't create a loop.
As a result, need to indirect control flow through a pointer notion.
Means you already have a 'Reader' monad at least, to deal with these look ups.
Relatively minor to then push that to a 'State' monad.
*)

datatype jump =
  GoTo "addr list" label
  | Call addr "addr option" label
  | IndCall addr "addr option" label

(*
From an analysis perspective, we are interested in collecting results at code points.
But effectively looking at a map from 'Loc' to abstract value.
Granularity of 'Loc' may change:
  \<bullet> Every code point
  \<bullet> Block 
  \<bullet> Function

This motivates mutable statements, as it gives you an identifier per location
at lowest level of granularity.

We can just model this as an array, gets extended with allocation,
cheap lookups & edits. But then we never edit?
*)



end
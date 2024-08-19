theory BASIL
  imports Stmt 
begin

datatype block =
  Block (label: string) (address: "int32 option") 
        (statements: "addr list") "addr option"

fun wf_block
  

(*
  Imperative code:
  - State will need to hold a series of collections, such as stmt
  - Can make it polymorphic, but I see little point atm.
  - Monadic operations to bind, etc.
*)

export_code wf_stmt wf_expr  in Scala


end
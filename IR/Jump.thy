theory Jump
  imports Stmt 
begin

section \<open>Immutable Jump\<close>

datatype jump =
  GoTo (targets: "nat list") (label: label)
  | DirectCall (proc: nat) (returnTarget: "nat option") (label: label)
  | IndirectCall (target: expr) (returnTarget: "nat option") (label: label)

end
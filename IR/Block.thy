theory Block
  imports Jump
begin 

section \<open>Immutable Block\<close>

datatype block =
  Block (label: string) 
        (address: "nat option") 
        (statements: "stmt list") 
        (jump: "jump")
        (incomingJumps: "jump set")
        (fallthrough: "jump option")

end
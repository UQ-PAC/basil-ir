theory Procedure
  imports Block
begin

section \<open>Immutable Procedure\<close>

datatype proc =
  Procedure (name: string)
            (address: "nat option")
            (entryBlock: "block option")
            (returnBlock: "block option")
            (blocks: "block set")

end
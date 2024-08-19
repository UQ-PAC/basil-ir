theory Test
  imports Int32
begin

class count =
  fixes to_int :: "'a \<Rightarrow> integer"
  assumes "\<And>x. to_int x > 0"

end
theory testeo
  imports Main
begin

fun sum :: "nat \<Rightarrow> nat \<Rightarrow>  nat\<Rightarrow> nat" where
  "sum a b c = a +b + c"

value "1 + (2::nat)"

value "sum 1 2 3"


end
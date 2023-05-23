section \<open>Plurality Module\<close>

theory abs_module
  imports "Component_Types/Electoral_Module"
 "Component_Types/Elimination_Module"
 "Component_Types/Social_Choice_Types/Profile"
begin


subsection \<open>Definition\<close>


(*abs_winner deberia ir luego a profile*)
fun abs_winner :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "abs_winner A p w =
  (finite_profile A p \<and> w \<in> A \<and> (has_majority p w))"

fun abs_score :: "'a Evaluation_Function" where
  "abs_score x A p =
    (if (abs_winner A p x) then 1 else 0)"

fun absolute:: "'a Electoral_Module" where
  "absolute A p = (max_eliminator abs_score) A p"



end
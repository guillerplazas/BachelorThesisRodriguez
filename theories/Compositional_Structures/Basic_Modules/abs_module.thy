section \<open>Plurality Module\<close>

theory abs_module
  imports "Component_Types/Electoral_Module"
 "Component_Types/Elimination_Module"
 "Component_Types/Social_Choice_Types/Profile"
 "Defer_Module"

begin


subsection \<open>Definition\<close>


(*Some functions might need reordering*)
fun abs_winner :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "abs_winner A p w =
  (finite_profile A p \<and> w \<in> A \<and> (has_majority p w))"

fun abs_score :: "'a Evaluation_Function" where
  "abs_score x A p =
    (if (abs_winner A p x) then 1 else 0)"

fun abs_existence:: "'a set \<Rightarrow> 'a Profile  \<Rightarrow> bool" where
  "abs_existence A p = (\<exists> x \<in> A . abs_winner A p x)"

(*default*)
fun absolute_max:: "'a Electoral_Module" where
  "absolute_max A p = (if (abs_existence A p) then ( max_eliminator abs_score A p) else defer_module A p)"

(*just a test*)
fun absolute_min:: "'a Electoral_Module" where
  "absolute_min A p = min_eliminator abs_score A p"






end
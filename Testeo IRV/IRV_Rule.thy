chapter \<open>Voting Rules\<close>

section \<open>IRV Rule\<close>

theory IRV_Rule
  imports "IRV_Module"
          "../Theories/Compositional_Structures/Defer_One_Loop_Composition"
begin



subsection \<open>Definition\<close>

fun IRV_rule :: "'a Electoral_Module" where
  "IRV_rule A p= ((min_eliminator IRV_score )\<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d) A p"


end
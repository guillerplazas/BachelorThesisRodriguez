chapter \<open>Voting Rules\<close>

section \<open>IRV Rule\<close>

theory IRV_Rule
  imports "IRV_Module"
          "../Theories/Compositional_Structures/Defer_One_Loop_Composition"
begin



subsection \<open>Definition\<close>

fun IRV_rule :: "'a Electoral_Module" where
  "IRV_rule A p= (((abs_eliminator \<triangleright> min_eliminator IRV_score )\<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d) \<triangleright> elect_module ) A p"


end
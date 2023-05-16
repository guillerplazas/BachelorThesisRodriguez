section \<open>IRV_Rule\<close>

theory IRV_Rule
  imports Pairwise_Majority_Rule
        "Compositional_Structures/Basic_Modules/abs_module"
          "Compositional_Structures/Defer_One_Loop_Composition"
begin

fun IRV_score :: "'a Evaluation_Function" where
  "IRV_score x A p = win_count p x"


(*Estructura cogida de Pairwise-Comp, debería servir para abs*)
(*Aqui por que tres definiciones?*)
fun abs_rule :: "'a Electoral_Module" where
  "abs_rule A p = elector absolute A p"

fun absolute' :: "'a Electoral_Module" where
"absolute' A p =
  ((min_eliminator abs_score) \<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d) A p"

fun abs_rule' :: "'a Electoral_Module" where
  "abs_rule' A p = iterelect absolute' A p"

(*Aqui acaban definiciones de absolute*)

fun IRV_rule :: "'a Electoral_Module" where
  "IRV_rule A p= (((abs_rule \<triangleright> min_eliminator IRV_score )\<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d)) A p"



end

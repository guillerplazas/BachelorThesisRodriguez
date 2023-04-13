section \<open>IRV Module\<close>

theory IRV_Module
  imports "../theories/Compositional_Structures/Basic Modules/Component_Types/Elimination_Module"
begin

subsection \<open>Definition\<close>

fun IRV_score :: "'a Evaluation_Function" where
  "IRV_score x A p = (\<Sum> win_count p x y)"

fun IRV :: "'a Electoral_Module" where
  "IRV A p = min_eliminator IRV_score A p"

end
section \<open>Plurality Module\<close>

theory abs_module
  imports "Component_Types/Electoral_Module"
 "Component_Types/Elimination_Module"
 "Component_Types/Social_Choice_Types/Profile"
 "Defer_Module"
  "Drop_Module"



begin


subsection \<open>Definition\<close>

fun eliminate_least_score :: "'a Evaluation_Function \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a Electoral_Module" where
  "eliminate_least_score e r A p =
    (if A = {} then ({}, {}, {})
     else
        (if card A = 1 then defer_module A p  
        else
        let scores = {e x A p | x. x \<in> A};
            min_score = Min scores;
            candidates_with_min_score = {x \<in> A. e x A p = min_score}
        in
            if candidates_with_min_score = {} then ({}, {}, A)
            else if card candidates_with_min_score = 1 then ({}, candidates_with_min_score, A-candidates_with_min_score)
            else
              let (_, to_eliminate, _) = drop_module 1 r candidates_with_min_score p
              in
                if to_eliminate = {} then ({},{},A)
                else ({}, to_eliminate, A - to_eliminate)))"



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
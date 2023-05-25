section \<open>IRV_Rule\<close>

theory IRV_Rule
  imports Pairwise_Majority_Rule
        "Compositional_Structures/Basic_Modules/abs_module"
          "Compositional_Structures/Defer_One_Loop_Composition"
begin

fun IRV_score :: "'a Evaluation_Function" where
  "IRV_score x A p = win_count p x"

(*Aqui acaban definiciones de absolute*)

fun IRV_rule :: "'a Electoral_Module" where
  "IRV_rule A p= (((absolute_max \<triangleright> min_eliminator IRV_score )\<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d)\<triangleright>elect_module) A p"

(*Multi_winner wrapper*)

fun multi_winner_IRV :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result" where
"multi_winner_IRV n A p =
  (if A = {} \<or> n > card A
   then Error
   else 
    (case IRV_rule3 A p of
      Error \<Rightarrow> Error
    | OK winner \<Rightarrow> 
      (case multi_winner_IRV (n - 1) (A - {winner}) p of
        Error \<Rightarrow> Error
      | OK winners \<Rightarrow> OK (insert winner winners))))"


(*
fun multi_winner_IRV_rule :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a set \<times> 'a set \<times> 'a set" where
  "multi_winner_IRV_rule 0 A p = ({}, A, {})" 
| "multi_winner_IRV_rule (Suc n) A p = (
    let (elected, rejected, deferred) = IRV_rule A p;
        (new_elected, new_rejected, new_deferred) = multi_winner_IRV_rule n (A - elected) p
    in (elected \<union> new_elected, rejected \<union> new_rejected, deferred \<union> new_deferred))"
*)
(*
fun multi_winner_IRV_rule :: "nat \<Rightarrow> 'a Electoral_Module" where
  "multi_winner_IRV_rule 0 A p = ({}, A, {})" 
| "multi_winner_IRV_rule (Suc n) A p = (
    let (elected, rejected, deferred) = IRV_rule A p;
        (new_elected, new_rejected, new_deferred) = multi_winner_IRV_rule n (A - elected) p
    in (elected \<union> new_elected, rejected \<union> new_rejected, new_deferred))" *)


(*Modelo-este debería estar mal
fun multi_winner_IRV_rule :: "nat \<Rightarrow> 'a Electoral_Module" where
  "multi_winner_IRV_rule 0 A p = ({}, A, {})" 
| "multi_winner_IRV_rule (Suc n) A p = (
    let (winners, not_losers, losers) = IRV_rule A p;
        (new_winners, new_not_losers, new_losers) = multi_winner_IRV_rule n (A - winners) p
    in (winners \<union> new_winners, new_not_losers, losers \<union> new_losers))" *)





(*Just for the purpose of modelling the absolute majority rule ;) *)
fun abs_rule :: "'a Electoral_Module" where
  "abs_rule A p = elector absolute_max A p"

text \<open>
  These last functions have been developed for test purposes. 
  They are commented now for perfomance purposes. 
\<close>

(*
fun absolute' :: "'a Electoral_Module" where
"absolute' A p =
  ((min_eliminator abs_score) \<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d) A p"

fun abs_rule' :: "'a Electoral_Module" where
  "abs_rule' A p = iterelect absolute' A p"

fun IRV_rule2 :: "'a Electoral_Module" where
  "IRV_rule2 A p= (((absolute_max \<triangleright> min_eliminator IRV_score )\<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d)) A p"

fun IRV_rule3 :: "'a Electoral_Module" where
  "IRV_rule3 A p= (((abs_rule \<triangleright> min_eliminator IRV_score )\<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d)) A p"

fun mid_step:: "'a Electoral_Module" where
  "mid_step A p = (absolute_max \<triangleright> min_eliminator IRV_score) A p "
*)

end

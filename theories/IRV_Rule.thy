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

(*Multi_winner wrapper*)
fun multi_winner_IRV_rule :: "nat \<Rightarrow> 'a Electoral_Module" where
  "multi_winner_IRV_rule 0 A p = ({}, A, {})"
| "multi_winner_IRV_rule (Suc n) A p = (
    let (winners, not_losers, losers) = IRV_rule A p;
        (new_winners, new_not_losers, new_losers) = multi_winner_IRV_rule n (A - winners) p
    in (winners \<union> new_winners, new_not_losers, losers \<union> new_losers))"



(*Proof while working here, change later*)

text \<open>
has_clones checks if there exist alternatives in the set A and profile P which are ranked identically by all voters - "clones"
\<close>

definition has_clones :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
  "has_clones A P \<equiv> \<exists>c. c \<subseteq> A \<and> (list_all (\<lambda>ps. \<forall>x \<in> c. \<forall>y \<in> c. (x, y) \<in> ps \<longleftrightarrow> (y, x) \<in> ps) P)"



(*definition satisfies_ICP_IRV :: "bool" where
  "satisfies_ICP_IRV \<equiv> \<forall>A P a c. c \<subseteq> A \<and> a \<in> A \<and> has_clones A (replace_alternative_with_clones a c P) \<Longrightarrow> 
  IRV_rule A P = IRV_rule (A - {a} \<union> c) (replace_alternative_with_clones a c P)"*)


fun replace_in_relation :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "replace_in_relation a c R = 
  {(if x = a then z else x, if y = a then z else y) | x y z. (x, y) \<in> R \<and> z \<in> c } \<union>
  {(x, y) | x y. (x, y) \<in> R \<and> x \<noteq> a \<and> y \<noteq> a}"


definition replace_alternative_with_clones :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Profile" where
  "replace_alternative_with_clones a c P = map (replace_in_relation a c) P"

definition ICP :: "'a Electoral_Module \<Rightarrow> bool" where
  "ICP m \<equiv> electoral_module m \<and>
    \<forall>A P a c. c \<subseteq> A \<and> a \<in> A \<and> has_clones A (replace_alternative_with_clones a c P) \<Longrightarrow>
      m A P = m (A - {a} \<union> c) (replace_alternative_with_clones a c P) "




end

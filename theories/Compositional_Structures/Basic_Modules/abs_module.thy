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

text \<open>
has_clones checks if there exist alternatives in the set A and profile P which are ranked identically by all voters - "clones"
\<close>

definition has_clones :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
  "has_clones A P \<equiv> \<exists>c. c \<subseteq> A \<and> (list_all (\<lambda>ps. \<forall>x \<in> c. \<forall>y \<in> c. (x, y) \<in> ps \<longleftrightarrow> (y, x) \<in> ps) P)"

definition satisfies_ICP_IRV :: "bool" where
  "satisfies_ICP_IRV \<equiv> \<forall>A P a c. c \<subseteq> A \<and> a \<in> A \<and> has_clones A (replace_alternative_with_clones a c P) \<Longrightarrow> 
  IRV_rule A P = IRV_rule (A - {a} \<union> c) (replace_alternative_with_clones a c P)"


fun replace_in_relation :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "replace_in_relation a c R = 
  {(if x = a then z else x, if y = a then z else y) | x y z. (x, y) \<in> R \<and> z \<in> c } \<union>
  {(x, y) | x y. (x, y) \<in> R \<and> x \<noteq> a \<and> y \<noteq> a}"


definition replace_alternative_with_clones :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Profile" where
  "replace_alternative_with_clones a c P = map (replace_in_relation a c) P"







end
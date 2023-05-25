section \<open>independence_of_clones\<close>

theory independence_of_clones
  imports 
        "Compositional_Structures/Basic_Modules/abs_module"
          "Compositional_Structures/Defer_One_Loop_Composition"
begin


definition is_directly_preferred_in_ballot :: "'a \<Rightarrow> 'a \<Rightarrow> 'a Preference_Relation \<Rightarrow> bool" where
  "is_directly_preferred_in_ballot a c r \<equiv> 
    (a, c) \<in> r \<and> (\<forall>b. (b \<noteq> a \<and> b \<noteq> c) \<longrightarrow> \<not> ((a, b) \<in> r \<and> (b, c) \<in> r))"

fun clones_exist :: "'a Profile \<Rightarrow> bool" where
"clones_exist p = 
  (\<exists>a b. a \<noteq> b \<and> 
    (\<forall>r \<in> set p. (is_directly_preferred_in_ballot a b r) \<or> (is_directly_preferred_in_ballot b a r)))"

definition has_clones :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
  "has_clones A p \<equiv> \<exists>c. c \<subseteq> A \<and> (list_all (\<lambda>ps. \<forall>x \<in> c. \<forall>y \<in> c. (x, y) \<in> ps \<longleftrightarrow> (y, x) \<in> ps) p)"

definition clone_up_rel :: "'a \<Rightarrow> 'a \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "clone_up_rel a b R = 
    {(if z = a then b else z, if w = a then b else w) | z w. (z, w) \<in> R} \<union> R \<union> {(a,b)}"

definition clone_down_rel :: "'a \<Rightarrow> 'a \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "clone_down_rel a b R = 
    {(if z = a then b else z, if w = a then b else w) | z w. (z, w) \<in> R} \<union> R \<union> {(b,a)}"

fun modify_profile_with_clones :: "'a Profile \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a Profile" where
"modify_profile_with_clones p a b = 
  map 
    (\<lambda>(i, rel). 
      if i mod 2 = 0 
      then clone_up_rel a b rel 
      else clone_down_rel a b rel
    ) (enumerate 0 p)"

fun clone_intro :: "('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result) \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> 'a Result" where
"clone_intro em A p x =
  (if A \<noteq> {} then 
    let a = (SOME m. m \<in> A) in
    let new_p = modify_profile_with_clones p a x in
    let new_A = A \<union> {x} in
    em new_A new_p
  else undefined)"


end
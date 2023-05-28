section \<open>independence_of_clones\<close>

theory independence_of_clones
  imports 
        "Compositional_Structures/Basic_Modules/abs_module"
begin

definition is_clone_set :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
  "is_clone_set A p \<equiv> \<forall>r \<in> set p. \<forall>a \<in> A. \<forall>b \<in> A. a \<noteq> b \<longrightarrow> ((a, b) \<in> r \<longleftrightarrow> (b, a) \<in> r)"

(* Non- reflexive
definition dir_pref_in_ballot :: "'a \<Rightarrow> 'a \<Rightarrow> 'a Preference_Relation \<Rightarrow> bool" where
  "dir_pref_in_ballot a c r \<equiv> 
    (a, c) \<in> r \<and> (\<forall>b. (b \<noteq> a \<and> b \<noteq> c) \<longrightarrow> \<not> ((a, b) \<in> r \<and> (b, c) \<in> r))"*)

definition dir_pref_in_ballot :: "'a \<Rightarrow> 'a \<Rightarrow> 'a Preference_Relation \<Rightarrow> bool" where
  "dir_pref_in_ballot a c r \<equiv> 
    a \<noteq> c \<and> (a, c) \<in> r \<and> (\<forall>b. (b \<noteq> a \<and> b \<noteq> c) \<longrightarrow> \<not> ((a, b) \<in> r \<and> (b, c) \<in> r))"


(*fun clones_exist :: "'a Profile \<Rightarrow> bool" where
"clones_exist p = 
  (\<exists>a b. a \<noteq> b \<and> 
    (\<forall>r \<in> set p. (dir_pref_in_ballot a b r) \<or> (dir_pref_in_ballot b a r)))"*)

fun clones_exist_in_A :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
"clones_exist_in_A A p = 
  (\<exists>a\<in>A. \<exists>b\<in>A. a \<noteq> b \<and> 
    (\<forall>r \<in> set p. (dir_pref_in_ballot a b r) \<or> (dir_pref_in_ballot b a r)))"



(*definition has_clones :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
  "has_clones A p \<equiv> \<exists>c. c \<subseteq> A \<and> (list_all (\<lambda>ps. \<forall>x \<in> c. \<forall>y \<in> c. (x, y) \<in> ps \<longleftrightarrow> (y, x) \<in> ps) p)"*)
(*
definition has_clones :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
  "has_clones A p \<equiv> \<exists>c. c \<subseteq> A \<and> (\<forall>x \<in> c. \<forall>y \<in> c. x \<noteq> y \<longrightarrow> (clones_exist [r \<leftarrow> p . dir_pref_in_ballot x y r]))"
 *)

(*
definition has_clones :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
  "has_clones A p \<equiv> \<exists>c. c \<subseteq> A \<and> (\<forall>x \<in> c. \<forall>y \<in> c. x \<noteq> y \<longrightarrow> clones_exist (filter (\<lambda>ps. (x, y) \<in> ps \<or> (y, x) \<in> ps) p))"
*)

definition clone_up_rel :: "'a \<Rightarrow> 'a \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "clone_up_rel a b R = 
    {(if z = a then b else z, if w = a then b else w) | z w. (z, w) \<in> R} \<union> R \<union> {(a,b)} \<union> {(b,b)}"

definition clone_down_rel :: "'a \<Rightarrow> 'a \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "clone_down_rel a b R = 
    {(if z = a then b else z, if w = a then b else w) | z w. (z, w) \<in> R} \<union> R \<union> {(b,a)}\<union> {(b,b)}"

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
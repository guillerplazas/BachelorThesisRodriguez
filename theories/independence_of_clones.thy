section \<open>independence_of_clones\<close>

theory independence_of_clones
  imports 
        "Compositional_Structures/Basic_Modules/abs_module"
begin

definition is_clone_set :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
  "is_clone_set A p \<equiv> \<forall>r \<in> set p. \<forall>a \<in> A. \<forall>b \<in> A. a \<noteq> b \<longrightarrow> ((a, b) \<in> r \<longleftrightarrow> (b, a) \<in> r)"

(*funciona*)
definition dir_pref_in_ballot :: "'a \<Rightarrow> 'a \<Rightarrow> 'a Preference_Relation \<Rightarrow> bool" where
  "dir_pref_in_ballot a c r \<equiv> 
    a \<noteq> c \<and> (a, c) \<in> r \<and> (\<forall>b. (b \<noteq> a \<and> b \<noteq> c) \<longrightarrow> \<not> ((a, b) \<in> r \<and> (b, c) \<in> r))"


fun clones_exist_in_A :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
"clones_exist_in_A A p = 
  (\<exists>a\<in>A. \<exists>b\<in>A. a \<noteq> b \<and> 
    (\<forall>r \<in> set p. (dir_pref_in_ballot a b r) \<or> (dir_pref_in_ballot b a r)))"

definition introduces_clone_in_candidate :: "'a \<Rightarrow> 'a \<Rightarrow> 'a Profile \<Rightarrow> 'a Profile \<Rightarrow> bool" where
  "introduces_clone_in_candidate a c p pc \<equiv> 
    a \<noteq> c \<and> 
    (\<forall>r \<in> set pc. (dir_pref_in_ballot a c r) \<or> (dir_pref_in_ballot c a r)) \<and>
    (\<forall>r \<in> set p. \<forall>r' \<in> set pc. \<forall>b d. b \<noteq> a \<and> b \<noteq> c \<and> d \<noteq> a \<and> d \<noteq> c \<longrightarrow> ((b, d) \<in> r \<longleftrightarrow> (b, d) \<in> r'))"


definition introduces_clone2 :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a Profile \<Rightarrow> 'a Profile \<Rightarrow> bool" where
  "introduces_clone2 A c p q \<equiv> \<forall> a \<in> A. a \<noteq> c \<and> (\<forall>r \<in> set q. if r \<in> set p then dir_pref_in_ballot a c r else dir_pref_in_ballot c a r)"

definition is_winner :: "'a \<Rightarrow> 'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
  "is_winner x em A p \<equiv> x \<in> elect_r (em A p)"

definition is_deferred :: "'a \<Rightarrow> 'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
  "is_deferred x em A p \<equiv> x \<in> defer_r (em A p)"

definition independence_of_clones :: "'a Electoral_Module \<Rightarrow> bool" where
  "independence_of_clones em \<equiv> 
    \<forall>A p pc. (\<exists> a \<in> elect em A p. \<exists>c. c \<notin> A \<and> 
      introduces_clone_in_candidate a c p pc 
      \<longrightarrow> (is_winner a em (A \<union> {c}) pc \<or> is_winner c em (A \<union> {c}) pc))"

definition independence_of_clones_deferred :: "'a Electoral_Module \<Rightarrow> bool" where
  "independence_of_clones_deferred em \<equiv> 
    \<forall>A p pc. (\<exists> a \<in> defer em A p. \<exists>c. c \<notin> A \<and> 
      introduces_clone_in_candidate a c p pc 
      \<longrightarrow> (is_deferred a em (A \<union> {c}) pc \<or> is_deferred c em (A \<union> {c}) pc))"

lemma dir_pref_excludes_inverse:
  assumes "dir_pref_in_ballot a b r" 
    and "linear_order_on A r" 
    and "a \<in> A" 
    and "b \<in> A"
  shows "\<not>(b, a) \<in> r"
proof
  assume "(b, a) \<in> r"
  moreover have "(a, b) \<in> r" 
    using assms(1) unfolding dir_pref_in_ballot_def by simp
  moreover have "a \<noteq> b" 
    using assms(1) unfolding dir_pref_in_ballot_def by simp
  ultimately show False 
    using assms(2) unfolding linear_order_on_def partial_order_on_def 
    by (metis antisym_def)
qed

lemma introduces_clone_implies_dir_pref:
  assumes "introduces_clone_in_candidate a c p pc"
  shows "\<forall>r \<in> set pc. dir_pref_in_ballot a c r \<or> dir_pref_in_ballot c a r"
  using assms
  unfolding introduces_clone_in_candidate_def
  by simp

lemma preservation_of_preferences:
  assumes "dir_pref_in_ballot a b r"
    and "linear_order_on A r"
    and "a \<in> A"
    and "b \<in> A"
    and "introduces_clone_in_candidate a c p pc"
    and "r \<in> set p"
    and "r' \<in> set pc"
  shows "(a, b) \<in> r' "
proof -
  have "dir_pref_in_ballot a c r' \<or> dir_pref_in_ballot c a r'"
    using assms(5) assms(7) unfolding introduces_clone_in_candidate_def by blast
  then show ?thesis
  proof
    assume ac: "dir_pref_in_ballot a c r'"
    then have "\<not>(c, b) \<in> r'"
      using assms(1) dir_pref_excludes_inverse[OF ac] assms(2) assms(3) assms(4) 
      by (metis assms(5) assms(6) assms(7) introduces_clone_in_candidate_def)
    then show ?thesis
      using ac assms(2) assms(3) assms(4) unfolding linear_order_on_def partial_order_on_def preorder_on_def
      by (metis total_on_def)
  next
    assume ca: "dir_pref_in_ballot c a r'"
    then have "\<not>(b, c) \<in> r'"
      using assms(1) dir_pref_excludes_inverse[OF assms(1)] assms(2) assms(3) assms(4) 
      by (metis assms(5) assms(6) assms(7) introduces_clone_in_candidate_def)
    then show ?thesis
      using ca assms(2) assms(3) assms(4) unfolding linear_order_on_def partial_order_on_def preorder_on_def
      by (metis total_on_def)
  qed
qed

lemma win_count_of_new_clone:
  assumes "introduces_clone_in_candidate a c p pc"
  shows "win_count pc c \<le> win_count p a"


(**)



(*
lemma preservation_of_preferences:
  assumes a1: "a \<noteq> b" 
      and a2: "(a, b) \<in> r" 
      and a3: "r \<in> set p" 
      and a4: "introduces_clone_in_candidate a c p pc"
  shows "\<exists>r' \<in> set pc. (a, b) \<in> r'"
proof -
  have dir_pref: "\<forall>r\<in>set pc. dir_pref_in_ballot a c r \<or> dir_pref_in_ballot c a r"
    using a4 unfolding introduces_clone_in_candidate_def by auto
  obtain r' where r'_def: "r' \<in> set pc \<and> ((a, c) \<in> r' \<or> (c, a) \<in> r')" 
    using dir_pref by blast
  hence "a \<noteq> c" using a1 by auto
  then have "(a, b) \<in> r'"
    using a2 r'_def a3 dir_pref_in_ballot_def by metis
  thus ?thesis using r'_def by blast
qed*)


(*
definition independence_of_clones :: "'a Electoral_Module \<Rightarrow> bool" where
  "independence_of_clones em \<equiv> 
    \<forall>A p a c q. is_winner a em A p \<and>  introduces_clone a c p q 
      \<longrightarrow> (is_winner a em (A \<union> {c}) q \<or> is_winner c em (A \<union> {c}) q)"

definition independence_of_clones :: "'a Electoral_Module \<Rightarrow> bool" where
  "independence_of_clones em \<equiv> 
    \<forall>A p c pc. 
      (\<exists>a. a \<in> elect em A p \<and> introduces_clone_in_candidate a c p pc) 
      \<longrightarrow> ((\<exists>a. a \<in> elect em (A \<union> {c}) pc) \<or> c \<in> elect em (A \<union> {c}) pc)"*)




(*Functional Prog*)
(*
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

fun clone_intro :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> 'a set \<times> 'a Profile" where
  "clone_intro A p a =
    (if a \<in> A then 
      let x = (SOME m. m \<notin> A) in
      let new_p = modify_profile_with_clones p a x in
      (A \<union> {x}, new_p)
    else (A, p))"
*)


(*

definition independence_of_clones :: "('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a set \<times> 'a set \<times> 'a set) \<Rightarrow> bool" where
"independence_of_clones em \<equiv>
  \<forall>A p w.
    case em A p of
      (A1, d, e) \<Rightarrow>
        if A1 = A \<and> d = {} \<and> e = {w} then
          let (A', p') = clone_intro A p w in
            case em A' p' of
              (A1', d', e') \<Rightarrow>
                if A1' = A' \<and> d' = {} then 
                  \<exists>w'. e' = {w'} \<and> (w' = w \<or> clones_exist_in_A {w', w} p')
                else False
        else False"
*)

(*w refers to winner, defined later
definition independence_of_clones :: "('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a set \<times> 'a set \<times> 'a set) \<Rightarrow> bool" where
"independence_of_clones em \<equiv>
  \<forall>A p.
    let (e, r, A1) = em A p in
    if \<exists>w. (e = {w} \<and> A1 = A - {w} \<and> r = {}) then
      let w = the_elem e; (A', p') = clone_intro A p w in
        case em A' p' of
          (e', r', A1') \<Rightarrow>
            A1' = A' \<and> r' = {} \<and> (\<exists>w'. e' = {w'} \<and> (w' = w \<or> clones_exist_in_A {w', w} p'))
    else False"*)


(*
definition independence_of_clones :: "('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a set \<times> 'a set \<times> 'a set) \<Rightarrow> bool" where
"independence_of_clones em \<equiv>
  \<forall>A p w.
    case em A p of
      (A1, d, e) \<Rightarrow>
        if A1 = A \<and> d = {} \<and> e = {w} then
          let (A', p') = clone_intro A p w in
            case em A' p' of
              (A1', d', e') \<Rightarrow>
                if A1' = A' \<and> d' = {} then 
                  \<exists>w'. e' = {w'} \<and> (w' = w \<or> clones_exist_in_A {w', w} p')
                else False
        else False"*)



(*

fun clone_intro2 :: "('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result) \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> 'a Result" where
"clone_intro2 em A p x =
  (if A \<noteq> {} then 
    let a = (SOME m. m \<in> A) in
    let new_p = modify_profile_with_clones p a x in
    let new_A = A \<union> {x} in
    em new_A new_p
  else undefined)"

definition same_result :: "('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result) \<Rightarrow> ('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result) \<Rightarrow> ('a Result \<Rightarrow> 'a) \<Rightarrow> bool" where
  "same_result em1 em2 voting_rule \<equiv> \<forall> A p. em1 A p = em2 A p \<longrightarrow> voting_rule (em1 A p) = voting_rule (em2 A p)"

definition same_result :: "('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result) \<Rightarrow> ('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result) \<Rightarrow> ('a Result \<Rightarrow> 'a) \<Rightarrow> bool" where
  "same_result em1 em2 voting_rule \<equiv> \<forall> A p. em1 A p = em2 A p \<longrightarrow> voting_rule (em1 A p) = voting_rule (em2 A p)"

definition same_result :: "('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result) \<Rightarrow> ('a Result \<Rightarrow> 'a) \<Rightarrow> bool" where
  "same_result em voting_rule \<equiv> \<forall> A p winner. em A p = OK winner \<longrightarrow> 
    (\<forall>a_clone. a_clone \<noteq> winner \<longrightarrow> em (insert a_clone A) (modify_profile_with_clones p winner a_clone) = em A p) \<longrightarrow> 
    voting_rule (em A p) = voting_rule (em (insert a_clone A) (modify_profile_with_clones p winner a_clone))"
*)
end
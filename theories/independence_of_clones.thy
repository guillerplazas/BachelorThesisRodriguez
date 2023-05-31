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

(*w refers to winner, defined later*)
definition independence_of_clones :: "('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a set \<times> 'a set \<times> 'a set) \<Rightarrow> bool" where
"independence_of_clones em \<equiv>
  \<forall>A p.
    let (e, r, A1) = em A p in
    if \<exists>w. (e = {w} \<and> A1 = A - {w} \<and> r = {}) then
      let w = the_elem e; (A', p') = clone_intro A p w in
        case em A' p' of
          (e', r', A1') \<Rightarrow>
            A1' = A' \<and> r' = {} \<and> (\<exists>w'. e' = {w'} \<and> (w' = w \<or> clones_exist_in_A {w', w} p'))
    else False"


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

end
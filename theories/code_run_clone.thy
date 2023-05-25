section \<open>code_run_clone\<close>

theory code_run_clone
  imports IRV_Rule
         
begin

text \<open>
Case 1: Strict clones
Voter 1: [c,b,a]
Voter 2: [c,b,a]
Voter 2: [c,b,a]
\<close>

(*Code Testing*)

text \<open>
Case 1: A wins first round
Ballot: Bottom [...] Top
Voter 1: [c,b,a]
Voter 2: [b,c,a]
Voter 2: [c,b,a]
\<close>



definition canA :: "char" where "canA = CHR ''a''"

definition canB :: "char" where  "canB = CHR ''b''"

definition canC :: "char" where "canC = CHR ''c''"

definition canX :: "char" where  "canX = CHR ''x''"



definition clone_up :: "'a \<Rightarrow> 'a \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "clone_up a b R = 
    {(if z = a then b else z, if w = a then b else w) | z w. (z, w) \<in> R} \<union> R \<union> {(a,b)}"

(* Defining the set of alternatives A *)
definition A :: "char set" where  "A = {canA, canB, canC}"

(* Defining the preference relation of the  voters *)
definition voter1_pref1 :: "(char \<times> char) set" where
  "voter1_pref1 = set [(canC, canB), (canB, canA),(canC, canA)]"

definition voter2_pref1 :: "(char \<times> char) set" where
  "voter2_pref1 = set [(canC, canB), (canB, canA),(canC, canA)]"

definition voter3_pref1 :: "(char \<times> char) set" where
  "voter3_pref1 = set [(canC, canB), (canB, canA),(canC, canA)]"

(* Defining the profile p *)
definition p1 :: "char Profile" where  "p1 = [voter1_pref1, voter2_pref1,voter3_pref1]"

(* Define the has_clones property *)

fun modify_profile_with_clones :: "'a Profile \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a Profile" where
"modify_profile_with_clones p a b = 
  map 
    (\<lambda>(i, rel). 
      if i mod 2 = 0 
      then clone_up_rel a b rel 
      else clone_down_rel a b rel
    ) (enumerate 0 p)"

value "modify_profile_with_clones p1  canA canX"


value "is_directly_preferred_in_ballot canB canC voter1_pref1"


value "always_directly_preferred p1"

(*fun is_directly_preferred_than ::
  "'a \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<preceq>\<^sub>d_ _" [50, 1000, 51] 50) where
    "a \<preceq>\<^sub>d r b = ((a, b) \<in> r \<and> (\<forall>c. c \<noteq> a \<and> c \<noteq> b \<longrightarrow> \<not> ((a, c) \<in> r \<and> (c, b) \<in> r)))"*)



fun has_clones_property ::"'a set \<Rightarrow>'a Profile \<Rightarrow> bool" where
    "has_clones_property A p = (has_clones A p)"

fun test:: "'a set \<Rightarrow> 'a Profile  \<Rightarrow> bool" where
  "test Aset pro = (has_clones Aset pro)"




value "test A p1"

(* Evaluate the has_clones property *)
value "has_clones A p1"

text \<open>
Case 2: clones not in order
Ballot: Bottom [...] Top
Voter 1: [b,a]
Voter 2: [b,a]
\<close>



(* Defining the preference relation of the  voters *)
definition voter1_pref2 :: "(char \<times> char) set" where
  "voter1_pref2 = set [(canB, canA)]"

definition voter2_pref2 :: "(char \<times> char) set" where
  "voter2_pref2 = set [(canA, canB)]"


(* Defining the profile p *)
definition p2 :: "char Profile" where  "p2 = [voter1_pref2, voter2_pref2]"

value "modify_profile_with_clones p2  canA canX"




definition canY :: "char" where "canY = CHR ''y''"


(*fun substitute_in_relation :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "substitute_in_relation a x y R =
    {(if z = a then x else if z = x then y else if z = y then x else z,
      if w = a then y else if w = x then x else if w = y then y else w) | z w. (z, w) \<in> R} \<union>
    {(x, y)}"*)

(*fun substitute_in_relation :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "substitute_in_relation a x y R =
    {(if z = a then x else if z = x then y else z,
      if w = a then y else if w = x then x else if w = y then y else w) | z w. (z, w) \<in> R \<and> (z, w) \<noteq> (x, y)} \<union>
    {(x, y)}"*)

(*fun substitute_in_relation :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "substitute_in_relation a x y R =
    {(if z = a then x else if z = x then y else z,
      if w = a then y else if w = x then y else if w = y then x else w) | z w. (z, w) \<in> R \<and> (z, w) \<noteq> (x, y)} \<union>
    {(x, y)}"*)

(*fun substitute_in_relation :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a Preference_Relation" where
  "substitute_in_relation a x y R =
    {(z, w) | z w. (z, w) \<in> R \<and> z \<noteq> a \<and> w \<noteq> a} 
    \<union> {(x, w) | w. (a, w) \<in> R \<and> w \<noteq> a} 
    \<union> {(z, x) | z. (z, a) \<in> R \<and> z \<noteq> a}
    \<union> {(y, w) | w. (a, w) \<in> R \<and> w \<noteq> a} 
    \<union> {(z, y) | z. (z, a) \<in> R \<and> z \<noteq> a}
    \<union> {(x, y), (y, x)}"*)



definition is_directly_preferred_in_ballot :: "'a \<Rightarrow> 'a \<Rightarrow> 'a Preference_Relation \<Rightarrow> bool" where
  "is_directly_preferred_in_ballot a c r \<equiv> 
    (a, c) \<in> r \<and> (\<forall>b. (b \<noteq> a \<and> b \<noteq> c) \<longrightarrow> \<not> ((a, b) \<in> r \<and> (b, c) \<in> r))"

fun clone_in_ballot :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a Preference_Relation" where
  "clone_in_ballot a x As r = {(z, w) \<in> r. z \<noteq> a \<and> w = a}"
(*
 \<union> "
  
  {} { \<forall> y \<in> A-{a}. (z, w) \<in> r.
}"*)

(*
fun clone_in_ballot :: "'a \<Rightarrow> 'a \<Rightarrow> 'a Preference_Relation\<Rightarrow>'a Preference_Relation" where
  "clone_in_ballot a x r = {(z, w) | z w. (z, w) \<in> r \<and> z \<noteq> a \<and> w \<noteq> a}  "*)




value " replace_candidate_in_relation canA canX voter2_pref2 "

fun substitute_candidates :: "'a Profile \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a Profile" where
  "substitute_candidates p a x y = map (substitute_in_relation a x y) p"


(*fun substitute_candidates_in_relation :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "substitute_candidates_in_relation a x y R =
    {(z, w) | z w. (z, w) \<in> R \<and> z \<noteq> a \<and> w \<noteq> a}
    \<union> {(x, y)}"*)

fun substitute_candidates_in_relation :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a Preference_Relation" where
  "substitute_candidates_in_relation a x y R =
    {(z, w) | z w. (z, w) \<in> R \<and> z \<noteq> a \<and> w \<noteq> a} 
    \<union> {(x, w) | (a, w) \<in> R \<and> w \<noteq> a} 
    \<union> {(z, x) | (z, a) \<in> R \<and> z \<noteq> a}
    \<union> {(y, w) | (a, w) \<in> R \<and> w \<noteq> a} 
    \<union> {(z, y) | (z, a) \<in> R \<and> z \<noteq> a}
    \<union> {(x, y), (y, x)}"

value "substitute_candidates_in_relation canA canX canY voter2_pref2"


end
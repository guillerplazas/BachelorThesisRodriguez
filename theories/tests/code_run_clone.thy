section \<open>code_run_clone\<close>

theory code_run_clone
  imports "../IRV_Rule"
          "../independence_of_clones"
         
begin

definition canA :: "char" where "canA = CHR ''a''"
definition canB :: "char" where "canB = CHR ''b''"
definition canC :: "char" where "canC = CHR ''c''"
definition canX :: "char" where "canX = CHR ''x''"

definition prevA :: "char set" where  "prevA = {canA, canB}"
definition A :: "char set" where  "A = {canA, canB, canC}"

text \<open>
Case 1: Strict clones
Voter 1: [c,b,a]
Voter 2: [c,b,a]
Voter 2: [c,b,a]
\<close>

definition prev_voter1_pref1 :: "(char \<times> char) set" where "prev_voter1_pref1 = set [(canC, canA),(canA, canA),(canC, canC)]"
definition prev_voter2_pref1 :: "(char \<times> char) set" where "prev_voter2_pref1 = set [(canC, canA),(canA, canA),(canC, canC)]"
definition prev_voter3_pref1 :: "(char \<times> char) set" where "prev_voter3_pref1 = set [(canC, canA),(canA, canA),(canC, canC)]"


definition voter1_pref1 :: "(char \<times> char) set" where "voter1_pref1 = set [(canC, canB), (canB, canA),(canC, canA),(canA, canA),(canB, canB),(canC, canC)]"
definition voter2_pref1 :: "(char \<times> char) set" where "voter2_pref1 = set [(canC, canB), (canA, canB),(canC, canA),(canA, canA),(canB, canB),(canC, canC)]"
definition voter3_pref1 :: "(char \<times> char) set" where "voter3_pref1 = set [(canC, canB), (canB, canA),(canC, canA),(canA, canA),(canB, canB),(canC, canC)]"

definition p1 :: "char Profile" where  "p1 = [voter1_pref1, voter2_pref1,voter3_pref1]"
definition prev_p1 :: "char Profile" where  "prev_p1 = [prev_voter1_pref1, prev_voter2_pref1,prev_voter3_pref1]"

value "introduces_clone canA canB prev_p1 p1"
value "loose_count_code p1 canA"
value "dir_pref_in_ballot canB canA voter1_pref1"
value "clones_exist p1"
value "clones_exist_in_A A p1"
value "modify_profile_with_clones p1  canA canX"
value "clone_intro A p1 canX"
value "SOME a. a \<in> A"
value "step_2 A p1"

value "is_directly_preferred_in_ballot canB canC voter1_pref1"
value "always_directly_preferred p1"


text \<open>
Case 2: clones not in order
Ballot: Bottom [...] Top
Voter 1: [b,a]
Voter 2: [b,a]
\<close>

definition voter1_pref2 :: "(char \<times> char) set" where "voter1_pref2 = set [(canB, canA),(canB, canB),(canA, canA)]"
definition voter2_pref2 :: "(char \<times> char) set" where "voter2_pref2 = set [(canA, canB),(canB, canB),(canA, canA)]"

definition p2 :: "char Profile" where  "p2 = [voter1_pref2, voter2_pref2]"

value "modify_profile_with_clones p2  canA canX"
value "win_count p2 canA"
value "loose_count_code p2 canA"


datatype 'a list = Nil | Cons 'a "'a list"

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app Nil ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev Nil = Nil" |
"rev (Cons x xs) = app (rev xs) (Cons x Nil)"

lemma rev_app [simp]: "rev(app xs ys) = app (rev ys) (rev xs)"
  apply(induction xs)
   apply(auto)

theorem rev_rev [simp]: "rev(rev xs) = xs"
  apply(induction xs)
  apply(auto)

end
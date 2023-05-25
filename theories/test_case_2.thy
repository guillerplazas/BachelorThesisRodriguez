section \<open>test_case_2\<close>

theory test_case_2
  imports IRV_Rule
          Sequential_Majority_Comparison
          Borda_Rule
          Copeland_Rule
begin

text \<open>
Case 2:
Ballot: Bottom [...] Top
Voter 1: [e,d,a,c,b]
Voter 2: [e,b,d,a,c]
Voter 3: [e,a,c,d,b]
Voter 4: [b,e,a,c,d]
Voter 5: [d,c,a,e,b]
Voter 6: [c,b,d,a,e]
\<close>

definition canA :: "char" where "canA = CHR ''a''"

definition canB :: "char" where "canB = CHR ''b''"

definition canC :: "char" where "canC = CHR ''c''"

definition canD :: "char" where "canD = CHR ''d''"

definition canE :: "char" where "canE = CHR ''e''"

(* Defining the set of alternatives A *)
definition A :: "char set" where  "A = {canA, canB, canC, canD ,canE}"


(* Defining the preference relation of the voters *)
definition voter1_pref2 :: "(char \<times> char) set" where
  "voter1_pref2 = set [(canE, canD), (canE, canA), (canE, canC), (canE, canB), (canD, canA), (canD, canC), (canD, canB), (canA, canC), (canA, canB), (canC, canB)]"

definition voter2_pref2 :: "(char \<times> char) set" where
  "voter2_pref2 = set [(canE, canB), (canE, canD), (canE, canA), (canE, canC), (canB, canD), (canB, canA), (canB, canC), (canD, canA), (canD, canC), (canA, canC)]"

definition voter3_pref2 :: "(char \<times> char) set" where
  "voter3_pref2 = set [(canE, canA), (canE, canC), (canE, canD), (canE, canB), (canA, canC), (canA, canD), (canA, canB), (canC, canD), (canC, canB), (canD, canB)]"

definition voter4_pref2 :: "(char \<times> char) set" where
  "voter4_pref2 = set [(canB, canE), (canB, canA), (canB, canC), (canB, canD), (canE, canA), (canE, canC), (canE, canD), (canA, canC), (canA, canD), (canC, canD)]"

definition voter5_pref2 :: "(char \<times> char) set" where
  "voter5_pref2 = set [(canD, canC), (canD, canA), (canD, canE), (canD, canB), (canC, canA), (canC, canE), (canC, canB), (canA, canE), (canA, canB), (canE, canB)]"

definition voter6_pref2 :: "(char \<times> char) set" where
  "voter6_pref2 = set [(canC, canB), (canC, canD), (canC, canA), (canC, canE), (canB, canD), (canB, canA), (canB, canE), (canD, canA), (canD, canE), (canA, canE)]"

(* Defining the profile p *)
definition p1 :: "char Profile" where  "p1 = [voter1_pref2, voter2_pref2,voter3_pref2,voter4_pref2,voter5_pref2,voter6_pref2]"

value "always_directly_preferred p1"
value "IRV_rule3 A p1"
value "mid_step A p1"
value "absolute_min A p1"
value "absolute_max A p1"
value "abs_winner A p1 canB"
value "abs_rule A p1"


value "is_directly_preferred_in_ballot canA canC voter1_pref2"

end
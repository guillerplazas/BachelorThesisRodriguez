section \<open>test_case_2\<close>

theory test_case_2
  imports "../IRV_Rule"
          
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

definition A :: "char set" where  "A = {canA, canB, canC, canD ,canE}"


definition voter1_pref2 :: "(char \<times> char) set" where
  "voter1_pref2 = set [(canE, canD), (canE, canA), (canE, canC), (canE, canB), (canD, canA), (canD, canC), (canD, canB), (canA, canC), (canA, canB), (canC, canB),
(canA, canA), (canB, canB) ,(canC, canC),(canD, canD),(canE, canE)]"

definition voter2_pref2 :: "(char \<times> char) set" where
  "voter2_pref2 = set [(canE, canB), (canE, canD), (canE, canA), (canE, canC), (canB, canD), (canB, canA), (canB, canC), (canD, canA), (canD, canC), (canA, canC),
(canA, canA), (canB, canB) ,(canC, canC),(canD, canD),(canE, canE)]"

definition voter3_pref2 :: "(char \<times> char) set" where
  "voter3_pref2 = set [(canE, canA), (canE, canC), (canE, canD), (canE, canB), (canA, canC), (canA, canD), (canA, canB), (canC, canD), (canC, canB), (canD, canB),
(canA, canA), (canB, canB) ,(canC, canC),(canD, canD),(canE, canE)]"

definition voter4_pref2 :: "(char \<times> char) set" where
  "voter4_pref2 = set [(canB, canE), (canB, canA), (canB, canC), (canB, canD), (canE, canA), (canE, canC), (canE, canD), (canA, canC), (canA, canD), (canC, canD),
  (canA, canA), (canB, canB) ,(canC, canC),(canD, canD),(canE, canE)]"

definition voter5_pref2 :: "(char \<times> char) set" where
  "voter5_pref2 = set [(canD, canC), (canD, canA), (canD, canE), (canD, canB), (canC, canA), (canC, canE), (canC, canB), (canA, canE), (canA, canB), (canE, canB),
(canA, canA), (canB, canB) ,(canC, canC),(canD, canD),(canE, canE)]"

definition voter6_pref2 :: "(char \<times> char) set" where
  "voter6_pref2 = set [(canC, canB), (canC, canD), (canC, canA), (canC, canE), (canB, canD), (canB, canA), (canB, canE), (canD, canA), (canD, canE), (canA, canE),
(canA, canA), (canB, canB) ,(canC, canC),(canD, canD),(canE, canE)]"

definition p1 :: "char Profile" where  "p1 = [voter1_pref2, voter2_pref2,voter3_pref2,voter4_pref2,voter5_pref2,voter6_pref2]"


value "IRV_rule A p1"
value "(mid_step\<triangleright>mid_step) A p1"
value "step_2 A p1"
value "(mid_step_2\<triangleright>mid_step_2) A p1"
value "absolute_min A p1"
value "absolute_max A p1"
value "abs_winner A p1 canB"
value "abs_rule A p1"

text \<open>
code:
a and c are clones
bottom[...]top 
[b,a,c]
[b,a,c]
[b,c,a]
[b,c,a]
[c,a,b]
[c,a,b]
\<close>

definition A3 :: "char set" where  "A3 = {canA, canB, canC}"

definition voter1_pref3 :: "(char \<times> char) set" where
  "voter1_pref3 = set [(canB, canA), (canB, canC), (canA, canC), (canA, canA), (canB, canB), (canC, canC)]"

definition voter2_pref3 :: "(char \<times> char) set" where
  "voter2_pref3 = set [(canB, canA), (canB, canC), (canA, canC), (canA, canA), (canB, canB), (canC, canC)]"

definition voter3_pref3 :: "(char \<times> char) set" where
  "voter3_pref3 = set [(canB, canC), (canB, canA), (canC, canA), (canA, canA), (canB, canB), (canC, canC)]"

definition voter4_pref3 :: "(char \<times> char) set" where
  "voter4_pref3 = set [(canB, canC), (canB, canA), (canC, canA), (canA, canA), (canB, canB), (canC, canC)]"

definition voter5_pref3 :: "(char \<times> char) set" where
  "voter5_pref3 = set [(canC, canA), (canC, canB), (canA, canB), (canA, canA), (canB, canB), (canC, canC)]"

definition voter6_pref3 :: "(char \<times> char) set" where
  "voter6_pref3 = set [(canC, canA), (canC, canB), (canA, canB), (canA, canA), (canB, canB), (canC, canC)]"

definition p3 :: "char Profile" where  
  "p3 = [voter1_pref3, voter2_pref3, voter3_pref3, voter4_pref3, voter5_pref3, voter6_pref3]"

value "mid_step_2 A3 p3"
value "drop_module 2  "
value "IRV_tie A3 p3"


end
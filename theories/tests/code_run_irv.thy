section \<open>code_run_irv\<close>

theory code_run_irv
  imports "../IRV_Rule"
begin

text \<open>
Case 1: A wins first round
Ballot: Bottom [...] Top
Voter 1: [c,b,a]
Voter 2: [b,c,a]
Voter 2: [c,b,a]
\<close>

definition canA :: "char" where "canA = CHR ''a''"
definition canB :: "char" where "canB = CHR ''b''"
definition canC :: "char" where "canC = CHR ''c''"

definition A :: "char set" where  "A = {canA, canB, canC}"

definition voter1_pref1 :: "(char \<times> char) set" where "voter1_pref1 = set [(canC, canB), (canB, canA),(canC, canA)]"
definition voter2_pref1 :: "(char \<times> char) set" where "voter2_pref1 = set [(canB, canC), (canC, canA),(canB, canA)]"
definition voter3_pref1 :: "(char \<times> char) set" where "voter3_pref1 = set [(canC, canB), (canB, canA),(canC, canA)]"

definition p1 :: "char Profile" where  "p1 = [voter1_pref1, voter2_pref1,voter3_pref1]"

value "IRV_rule A p1"
value "profile A p1"

text \<open>Other test made, commented for performance\<close>
(*
value "win_count p1 canA"
value "has_majority p1 canA"
value "abs_winner A1 p1 canB"
value "absolute A1 p1"
value "abs_rule A1 p1"
value "IRV_rule3 A1 p1"
(*value "IRV_Rule A1 p1"
value "IRV_Rule2 A1 p1"
value "prefer_count p1 canA canB"
value "borda_score canA A1 p1"
value "borda_rule A1 p1"
value "copeland_rule A1 p1"
value "abs_rule' A1 p1"
value "IRV_Rule3 A1 p1"
value "run_absolute A1 p1"
value " A1 p1"*)
*)

text \<open>
Case 2: C eliminated first, then A wins
Voter 1: [a,b,c]
Voter 2: [b,a,c]
Voter 3: [c,a,b]
\<close>

definition voter1_pref2 :: "(char \<times> char) set" where "voter1_pref2 = set [(canB, canA), (canC, canA),(canC, canB)]"
definition voter2_pref2 :: "(char \<times> char) set" where "voter2_pref2 = set [(canA, canB), (canC, canB),(canC, canA)]"
definition voter3_pref2 :: "(char \<times> char) set" where "voter3_pref2 = set [(canA, canC), (canB, canC),(canB, canA)]"

(* Defining the profile p *)
definition p2 :: "char Profile" where  "p2 = [voter1_pref2, voter2_pref2,voter3_pref2]"

value "abs_rule A p2"
value "IRV_rule A p2"
value "IRV_score canA A p2"


end
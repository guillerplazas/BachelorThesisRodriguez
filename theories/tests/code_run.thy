section \<open>code_run\<close>

theory code_run
  imports "../IRV_Rule"
          "../Sequential_Majority_Comparison"
          "../Borda_Rule"
          "../Copeland_Rule"
begin

text \<open>
File created to develop the input for the value command and test some rules.
\<close>

text \<open>
Case 1: A wins first round
Voter 1: [c,b,a]
Voter 2: [b,c,a]
Voter 2: [c,b,a]
\<close>

text \<open>Definition of alternatives A\<close>
definition canA :: "char" where "canA = CHR ''a''"
definition canB :: "char" where "canB = CHR ''b''"
definition canC :: "char" where "canC = CHR ''c''"

definition A1 :: "char set" where  "A1 = {canA, canB,canC}"

text \<open>Definition of Preference_Profiles\<close>
definition voter1_pref1 :: "(char \<times> char) set" where "voter1_pref1 = set [(canB, canA)]"
definition voter2_pref1 :: "(char \<times> char) set" where "voter2_pref1 = set [(canB, canA)]"

text \<open>Definition of profile p\<close>
definition p1 :: "char Profile" where  "p1 = [voter1_pref1, voter2_pref1]"

text \<open>Possible value commands. Commented to help performance\<close>
(*value "win_count p1 canA"
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

end
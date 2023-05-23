section \<open>code_run_multi\<close>

theory code_run_multi
  imports IRV_Rule
begin

(*Code Testing*)

text \<open>
Case 1: 2 winners
   A wins first round
  b wins second
Voter 1: [a,b,c]
Voter 2: [a,c,b]
Voter 2: [b,a,c]
\<close>

(* Defining the set of alternatives A *)
definition A1 :: "char set" where
  "A1 = {CHR ''a'', CHR ''b'', CHR ''c''}"

(* Defining the preference relation for the first voter *)
definition voter1_pref1 :: "(char \<times> char) set" where
  "voter1_pref1 = set [(CHR ''a'', CHR ''b''), (CHR ''a'', CHR ''c''), (CHR ''b'', CHR ''c'')]"

(* Defining the preference relation for the second voter *)
definition voter2_pref1 :: "(char \<times> char) set" where
  "voter2_pref1 = set [(CHR ''a'',CHR ''c''), (CHR ''a'',CHR ''b''), (CHR ''c'',CHR ''b'')]"

(* Defining the preference relation for the second voter *)
definition voter3_pref1 :: "(char \<times> char) set" where
  "voter3_pref1 = set [(CHR ''b'',CHR ''a''), (CHR ''b'',CHR ''c''), (CHR ''a'',CHR ''c'')]"

(* Defining the profile p *)
definition p1 :: "char Profile" where
  "p1 = [voter1_pref1, voter2_pref1,voter3_pref1]"

value "multi_winner_IRV_rule (Suc (Suc 0))  A1 p1"

text \<open>
Case 2: C eliminated first, then A wins
Voter 1: [a,b,c]
Voter 2: [b,a,c]
Voter 3: [c,a,b]
\<close>

definition A2 :: "char set" where
  "A2 = {CHR ''a'', CHR ''b'', CHR ''c''}"

(* Defining the preference relation for the first voter *)
definition voter1_pref2 :: "(char \<times> char) set" where
  "voter1_pref2 = set [(CHR ''a'', CHR ''b''), (CHR ''a'', CHR ''c''), (CHR ''b'', CHR ''c'')]"

(* Defining the preference relation for the second voter *)
definition voter2_pref2 :: "(char \<times> char) set" where
  "voter2_pref2 = set [(CHR ''b'',CHR ''a''), (CHR ''b'',CHR ''c''), (CHR ''a'',CHR ''c'')]"

(* Defining the preference relation for the second voter *)
definition voter3_pref2 :: "(char \<times> char) set" where
  "voter3_pref2 = set [(CHR ''c'',CHR ''a''), (CHR ''c'',CHR ''b''), (CHR ''a'',CHR ''b'')]"

(* Defining the profile p *)
definition p2 :: "char Profile" where
  "p2 = [voter1_pref2, voter2_pref2,voter3_pref2]"

value "IRV_Rule A2 p2"

end
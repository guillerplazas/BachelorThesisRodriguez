section \<open>code_run\<close>

theory code_run
  imports IRV_Rule
begin

(*Code Testing*)

(* Defining the set of alternatives A *)
definition A :: "char set" where
  "A = {CHR ''a'', CHR ''b'', CHR ''c''}"

(* Defining the preference relation for the first voter *)
definition voter1_pref :: "(char \<times> char) set" where
  "voter1_pref = set [(CHR ''a'', CHR ''b''), (CHR ''a'', CHR ''c''), (CHR ''b'', CHR ''c'')]"

(* Defining the preference relation for the second voter *)
definition voter2_pref :: "(char \<times> char) set" where
  "voter2_pref = set [(CHR ''a'',CHR ''c''), (CHR ''a'',CHR ''b''), (CHR ''c'',CHR ''b'')]"

(* Defining the preference relation for the second voter *)
definition voter3_pref :: "(char \<times> char) set" where
  "voter3_pref = set [(CHR ''b'',CHR ''a''), (CHR ''b'',CHR ''c''), (CHR ''a'',CHR ''c'')]"

(* Defining the profile p *)
definition p :: "char Profile" where
  "p = [voter1_pref, voter2_pref,voter3_pref]"

value "IRV_Rule A p"

end
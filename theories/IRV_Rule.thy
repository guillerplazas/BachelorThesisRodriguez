section \<open>IRV_Rule\<close>

theory IRV_Rule
  imports Pairwise_Majority_Rule
        "Compositional_Structures/Basic_Modules/abs_module"
          "Compositional_Structures/Defer_One_Loop_Composition"
          "Compositional_Structures/Basic_Modules/drop_module"
begin

fun IRV_score :: "'a Evaluation_Function" where
  "IRV_score x A p = win_count p x"

fun IRV_rule_drop :: "'a Preference_Relation \<Rightarrow> 'a Electoral_Module" where
  "IRV_rule_drop r A p= (((absolute_max \<triangleright> ( eliminate_least_score IRV_score r) )\<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d)\<triangleright> elect_module) A p"

fun IRV_step_drop_test ::"'a Preference_Relation \<Rightarrow> 'a Electoral_Module" where
  "IRV_step_drop_test r A p=(absolute_max \<triangleright>  eliminate_least_score IRV_score r) A p "

fun IRV_step_drop ::"'a Preference_Relation \<Rightarrow> 'a Electoral_Module" where
  "IRV_step_drop r A p=eliminate_least_score IRV_score r A p "



fun IRV_rule :: "'a Electoral_Module" where
  "IRV_rule A p= (((absolute_max \<triangleright> min_eliminator IRV_score )\<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d)\<triangleright> elect_module) A p"


(*Garbage *)

(*
fun sum_IRV_score :: "'a::finite set \<Rightarrow> 'a Profile \<Rightarrow> nat" where
  "sum_IRV_score A p =  (\<Sum> y \<in> A. (IRV_score y A p))"

fun max_IRV_score :: "'a::finite set \<Rightarrow> 'a Profile \<Rightarrow> nat" where
  "max_IRV_score A p = Max ((\<lambda> a. IRV_score a A p) ` A)"

fun step_2 :: "'a Electoral_Module" where
  "step_2 A p= min_eliminator IRV_score_2 A p*)


(*fun mid_step :: "'a Electoral_Module" where
  "mid_step A p= (absolute_max \<triangleright> min_eliminator IRV_score) A p"*)

(*fun IRV_tie :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
  "IRV_tie A p = (\<exists>x \<in> A. \<exists>y \<in> A. x \<noteq> y \<and> win_count p x = win_count p y \<and> 
                   (\<forall>z \<in> A. z \<noteq> x \<longrightarrow> z \<noteq> y \<longrightarrow> win_count p z \<ge> win_count p x))"
*)

(*fun IRV_score_2 :: "'a Evaluation_Function" where
  "IRV_score_2 x A p =
     (if (\<exists>y \<in> A. x \<noteq> y \<and> win_count p x = win_count p y \<and>
                  (\<forall>z \<in> A. (z \<noteq> x \<longrightarrow> z \<noteq> y \<longrightarrow> win_count p z \<ge> win_count p x)))
      then win_count p x - loose_count_code p x
      else win_count p x)"*)

(*
fun IRV_tie_cand :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
  "IRV_tie_cand x A p =
     (if (\<exists>y \<in> A. x \<noteq> y \<and> win_count p x = win_count p y \<and>
                  (\<forall>z \<in> A. (z \<noteq> x \<longrightarrow> z \<noteq> y \<longrightarrow> win_count p z \<ge> win_count p x)))
      then True
      else False)"*)

(*
lemma not_both_lowest_score_after_clone:
  fixes p :: "'a Profile"
    and a :: 'a
    and c :: 'a
  assumes introduces_clone: "introduces_clone_in_candidate a c p pc"
  assumes Ac_def: "Ac = A \<union> {c}"
  shows "\<not>(IRV_score_2 a Ac pc = Min {IRV_score_2 x Ac pc | x. x \<in> Ac}) \<and>
         \<not>(IRV_score_2 c Ac pc = Min {IRV_score_2 x Ac pc | x. x \<in> Ac})"
proof
  assume "IRV_score_2 a Ac pc = Min {IRV_score_2 x Ac pc | x. x \<in> Ac} \<and>
          IRV_score_2 c Ac pc = Min {IRV_score_2 x Ac pc | x. x \<in> Ac}"
  then have "IRV_score_2 a Ac pc = Min {IRV_score_2 x Ac pc | x. x \<in> Ac}" 
    and "IRV_score_2 c Ac pc = Min {IRV_score_2 x Ac pc | x. x \<in> Ac}" by simp_all
  moreover have "win_count p a = Min {win_count p x | x. x \<in> Ac}" 
      proof -
    have "introduces_clone_in_candidate a c p pc"
      using introduces_clone by simp
    moreover {
      fix b r r'
      assume "dir_pref_in_ballot a b r" "linear_order_on Ac r" "a \<in> Ac" "b \<in> Ac"
             "r \<in> set p" "r' \<in> set pc"
      with introduces_clone preservation_of_preferences Ac_def
      have "(a, b) \<in> r'"
        by auto
    }
    ultimately show ?thesis
      using Ac_def by simp
  qed
  moreover have "loose_count_code p a = Min {loose_count_code p x | x. x \<in> Ac}"
    and "loose_count_code p c = Min {loose_count_code p x | x. x \<in> Ac}"
    sorry  (* Here you need to provide the proof for this statement *)
  ultimately have "IRV_score_2 a Ac pc - loose_count_code p a = Min {IRV_score_2 x Ac pc - loose_count_code p x | x. x \<in> Ac}"
    and "IRV_score_2 c Ac pc - loose_count_code p c = Min {IRV_score_2 x Ac pc - loose_count_code p x | x. x \<in> Ac}"
    by simp_all
  then have "win_count p a - loose_count_code p a = Min {win_count p x - loose_count_code p x | x. x \<in> Ac}"
    and "win_count p c - loose_count_code p c = Min {win_count p x - loose_count_code p x | x. x \<in> Ac}"
    by (metis diff_diff_add nat_diff_split)+
  moreover have "win_count p a - loose_count_code p a < win_count p c - loose_count_code p c"
    sorry  (* Here you need to provide the proof for this statement *)
  ultimately show False by simp
qed
*)







(*
fun bulk_eliminator :: "'a Evaluation_Function \<Rightarrow> 'a Electoral_Module" where
  "bulk_eliminator e A p =
    (let
      scores = {e x A p | x. x \<in> A};
      min_score = Min scores;
      second_min_score = Min (scores - {min_score});
      losers = {x \<in> A. e x A p < second_min_score}
    in
      if losers = {} then ({}, {}, A) else ({}, losers, A - losers))"*)

(*
fun single_min_eliminator :: "'a::finite Evaluation_Function \<Rightarrow> 'a Electoral_Module" where
  "single_min_eliminator e A p =
    (if A \<noteq> {} then
       let loser = select_one_with_min_score e A p in
       ({}, {loser}, A - {loser})
     else
       ({}, {}, A))"*)



(*Para mejorar IRV*)
(*
fun select_one_loser :: "'a::finite set \<Rightarrow> 'a list \<Rightarrow> 'a" where
  "select_one_loser A p =
    (let
      loser_scores = map (\<lambda>a. (a, sum_IRV_score {a} p)) (set A);
      sorted_losers = sort_key snd loser_scores
     in
      fst (hd sorted_losers))"*)


(*
fun custom_eliminator :: "'a set \<Rightarrow> 'a Electoral_Module" where
  "custom_eliminator losers A p = 
    (if (losers \<subseteq> A) then ({}, losers, A - losers) 
    else ({}, {}, A))"

fun step_2_modified :: "'a::finite Electoral_Module" where
  "step_2_modified A p =
    (let max_score = max_IRV_score A p;
         losers = {a \<in> A . sum_IRV_score {a} p < max_score}
     in custom_eliminator losers A p)"
*)

(*
fun sorted_list_of_set :: "('a::{linorder}) set \<Rightarrow> 'a list" where
  "sorted_list_of_set A = sort_key (\<lambda>x. x) (sorted_list_of_set A)"*)
(*
fun lexicographic_number :: "('a::{linorder}) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "lexicographic_number x sorted_list =
    (THE i. i < length sorted_list \<and> sorted_list ! i = x)"
*)
(*
fun lexicographic_IRV_score :: "'a::{linorder, finite} Evaluation_Function" where
  "lexicographic_IRV_score x A p =
    win_count p x * (card A + 1) + le"

fun sorted_list_of_set :: "('a::{linorder}) set \<Rightarrow> 'a list" where
  "sorted_list_of_set A = sort_key (\<lambda>x. x) (set A)" 

fun lexicographic_number :: "('a::{linorder}) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "lexicographic_number x sorted_list =
    (THE i. i < length sorted_list \<and> sorted_list ! i = x)"

fun lexicographic_IRV_score :: "'a::{linorder, finite} Evaluation_Function" where
  "lexicographic_IRV_score x A p =
     win_count p x * card A + lexicographic_tie_breaker x"

fun IRV_rule_with_lexicographic :: "'a::{linorder, finite} Electoral_Module" where
  "IRV_rule_with_lexicographic A p =
    (((absolute_max \<triangleright> single_eliminator lexicographic_IRV_score )\<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d)\<triangleright> elect_module) A p"
*)




(*
fun mid_step_2 :: "'a Electoral_Module" where
  "mid_step_2 A p= (absolute_max \<triangleright> step_2 ) A p"*)








(*
lemma mid_step_satisfies_independence_of_clones_deferred:
  shows "independence_of_clones_deferred mid_step"
proof (unfold independence_of_clones_deferred_def, clarify)
  fix A :: "'a set" and p :: "'a Profile" and a c pc
  assume defer_a: "a \<in> defer mid_step A p"
    and clone: "c \<notin> A"
    and introduces: "introduces_clone_in_candidate a c p pc"
  let ?B = "A \<union> {c}"
  
  have "\<exists>a'\<in>defer mid_step A p. \<exists>c. c \<notin> A \<and> introduces_clone_in_candidate a' c p pc"
    using defer_a clone introduces by blast
  then obtain a' where a'_in_defer: "a' \<in> defer mid_step A p" and c_notin_A: "c \<notin> A" and introduces_a': "introduces_clone_in_candidate a' c p pc" by auto

  have "a' \<in> defer mid_step ?B pc"
    using a'_in_defer by (simp add: defer_mid_step_def)
  moreover have "a' \<notin> defer mid_step ?B pc"
  proof
    assume "a' \<in> defer mid_step ?B pc"
    then have "a' \<in> defer mid_step A pc"
      using c_notin_A introduces_a' by (simp add: defer_mid_step_def)
    then show False
      using a'_in_defer by contradiction
  qed
  ultimately show False by simp
qed*)



















(*
lemma new_winner_is_clone:
  assumes "independence_of_clones em"
      and "em A p = ({w}, d, A1)"
  shows "\<exists>w'. (let (A', p') = clone_intro A p w in em A' p' = ({w'}, {}, A')) \<and> (w' = w \<or> clones_exist_in_A {w', w} p')"
proof -
  obtain A' p' where clone: "clone_intro A p w = (A', p')" by (cases "clone_intro A p w")
  obtain e' d' A1' where A': "em A' p' = (e', d', A1')" by (cases "em A' p'")
  have "A1' = A' \<and> d' = {} \<and> (\<exists>w'. e' = {w'} \<and> (w' = w \<or> clones_exist_in_A {w', w} p'))"
    using assms clone A' unfolding independence_of_clones_def by blast
  thus ?thesis by (metis A' prod.collapse)
qed*)

(*
lemma IRV_satisfies_independence_of_clones: "independence_of_clones IRV_rule"



lemma IRV_satisfies_independence_of_clones:
  assumes "independence_of_clones IRV_rule"
  shows "\<forall>A p w. case IRV_rule A p of (e, r, A1) \<Rightarrow> 
         if A1 = A \<and> r = {} \<and> e = {w} then
           let (A', p') = clone_intro A p w in
             case IRV_rule A' p' of
               (e', r', A1') \<Rightarrow>
                 if A1' = A' \<and> r' = {} then 
                   \<exists>w'. e' = {w'} \<and> (w' = w \<or> clones_exist_in_A {w', w} p')
                 else False
         else False"*)
(*
theorem clone_preserves_high_score:
  assumes 
    "is_winner a (step_2) A p"
    "introduces_clone_in_candidate a c p pc"
  shows 
    "\<not>(score_a_pc < min_score_except_ac \<and> score_c_pc < min_score_except_ac)"
proof -
  (* Define the scores of a in p, a in pc, and c in pc *)
  let ?score_a_p = "IRV_score_2 a A p"
  let ?score_a_pc = "IRV_score_2 a (A \<union> {c}) pc"
  let ?score_c_pc = "IRV_score_2 c (A \<union> {c}) pc"

  (* Define the minimum score in pc excluding a and c *)
  let ?min_score_except_ac = "Min {IRV_score_2 x (A \<union> {c}) pc |x. x \<in> A \<union> {c} \<and> x \<noteq> a \<and> x \<noteq> c}"

  (* Step 1: Show that the score of a in the modified profile pc can't decrease significantly *)
  have score_a_preserved: "?score_a_pc \<ge> ?score_a_p - k" 
  proof -



  (* Count the number of ballots where a is the winner in p *)
  let ?win_a_p = "win_count p a"
  (* Count the number of ballots where a is the winner in pc *)
  let ?win_a_pc = "win_count pc a"
  (* Count the number of ballots where a is the least preferred in p *)
  let ?loose_a_p = "loose_count p a"
  (* Count the number of ballots where a is the least preferred in pc *)
  let ?loose_a_pc = "loose_count pc a"
  let ?k1 = "win_count p a"   (* Maximum possible change in win_count is bounded by the original win_count *)
  let ?k2 = "loose_count_code p a"  (* Maximum possible change in loss_count is bounded by the original loss_count *)
 have win_count_close: "?win_a_pc \<ge> ?win_a_p - ?k1"
proof -
  let ?k1 = 1 (* Arbitrarily set k1 to 1 *)
  
  have win_relation: "win_count pc a = win_count p a + card {i::nat. i < length pc \<and> above (pc!i) a = {a, c}}"
    using assms(2) preservation_of_preferences by ...
    
  (* The additional wins should not be less than ?k1 *)
  have "card {i::nat. i < length pc \<and> above (pc!i) a = {a, c}} \<ge> ?k1" by ...
  
  have "?win_a_pc = win_count pc a"
    by simp
  also have "... = win_count p a + card {i::nat. i < length pc \<and> above (pc!i) a = {a, c}}"
    using win_relation
    by simp
  also have "... \<ge> ?win_a_p - ?k1"
    by simp
  finally show "?win_a_pc \<ge> ?win_a_p - ?k1" .
qed
  have loose_count_close: "?loose_a_pc \<ge> ?loose_a_p - ?k2" using assms(2) preservation_of_preferences by ...

  have "?score_a_pc = ?win_a_pc - ?loose_a_pc" by simp
  also have "... \<ge> ?win_a_p - ?k1 - (?loose_a_p - ?k2)" using win_count_close loose_count_close by simp
  also have "... = ?score_a_p - (?k1 + ?k2)" by simp
  finally show "?score_a_pc \<ge> ?score_a_p - (?k1 + ?k2)" .
qed
  (* Step 2: Show that the score of the clone c will be close to the score of a *)
  have score_c_close_to_a: "?score_c_pc \<ge> ?score_a_p - k" for some constant k ...
    using assms(2) preservation_of_preferences ...

  (* Step 3: Conclude that if score_a_p was the highest, neither score_a_pc nor score_c_pc can be the lowest in pc *)
  have "?score_a_pc \<ge> ?min_score_except_ac \<and> ?score_c_pc \<ge> ?min_score_except_ac"
    using score_a_preserved score_c_close_to_a ...

  (* This implies that neither a nor c has the lowest score in pc *)
  show "\<not>(score_a_pc < ?min_score_except_ac \<and> score_c_pc < ?min_score_except_ac)" by simp
qed*)



(*
lemma IRV_satisfies_independence_of_clones:
  shows "independence_of_clones IRV_rule"
unfolding independence_of_clones_def
proof (clarify)
  fix A :: "'a set" and p :: "'a Profile" and a c pc
  assume winner: "a \<in> elect IRV_rule A p"
  and clone: "c \<notin> A"
  and introduces: "introduces_clone_in_candidate a c p pc"
  let ?B = "A \<union> {c}"
  assume B_election: "\<exists> a \<in> elect IRV_rule A p. \<exists>c. c \<notin> A \<and> introduces_clone_in_candidate a c p pc"
  hence "a \<in> elect IRV_rule ?B pc \<or> c \<in> elect IRV_rule ?B pc"
  proof (cases "IRV_rule ?B pc")
    case (fields winners losers remaining)
    then have "a \<in> winners \<or> c \<in> winners" using introduces unfolding introduces_clone_in_candidate_def by auto
    then show ?thesis unfolding is_winner_def by blast
  qed
qed*)









(*Proof mas avanzada*)
(*
lemma IRV_satisfies_independence_of_clones:
  shows "independence_of_clones IRV_rule"
unfolding independence_of_clones_def
proof (clarify)
  fix A :: "'a set" and p :: "'a Profile" and winner :: 'a
  assume IRV_winner: "IRV_rule A p = ({winner}, A-{winner}, {})"
  let ?clone = "clone_intro A p winner"
  obtain e' r' where rule_def: "IRV_rule (fst ?clone) (snd ?clone) = (e', r', {})"
    using prod_cases3 by blast
  have "r' = {}" using rule_def by auto
  moreover have "\<exists>w'. e' = {w'} \<and> (w' = winner \<or> clones_exist_in_A {w', winner} (snd ?clone))" 
  proof (cases "e' = {winner}")
    case True
    then show ?thesis by auto
  next
    case False
    then obtain new_winner where new_winner_def: "e' = {new_winner}" by fastforce
    have "new_winner = winner \<or> clones_exist_in_A {new_winner, winner} (snd ?clone)"
    proof (cases "new_winner = winner")
      case True
      then show ?thesis by simp
    next
      case False
      then have "clones_exist_in_A {new_winner, winner} (snd ?clone)" 
        using new_winner_def False rule_def IRV_winner by simp
      then show ?thesis by simp
    qed
    then show ?thesis using new_winner_def by auto
  qed
  ultimately show "r' = {} \<and> (\<exists>w'. e' = {w'} \<and> (w' = winner \<or> clones_exist_in_A {w', winner} (snd ?clone)))"
    by auto
qed
*)











(*Multi_winner wrapper*)
(*
fun multi_winner_IRV :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result" where
"multi_winner_IRV n A p =
  (if A = {} \<or> n > card A
   then Error
   else 
    (case IRV_rule3 A p of
      Error \<Rightarrow> Error
    | OK winner \<Rightarrow> 
      (case multi_winner_IRV (n - 1) (A - {winner}) p of
        Error \<Rightarrow> Error
      | OK winners \<Rightarrow> OK (insert winner winners))))"
*)

(*
fun multi_winner_IRV_rule :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a set \<times> 'a set \<times> 'a set" where
  "multi_winner_IRV_rule 0 A p = ({}, A, {})" 
| "multi_winner_IRV_rule (Suc n) A p = (
    let (elected, rejected, deferred) = IRV_rule A p;
        (new_elected, new_rejected, new_deferred) = multi_winner_IRV_rule n (A - elected) p
    in (elected \<union> new_elected, rejected \<union> new_rejected, deferred \<union> new_deferred))"
*)
(*
fun multi_winner_IRV_rule :: "nat \<Rightarrow> 'a Electoral_Module" where
  "multi_winner_IRV_rule 0 A p = ({}, A, {})" 
| "multi_winner_IRV_rule (Suc n) A p = (
    let (elected, rejected, deferred) = IRV_rule A p;
        (new_elected, new_rejected, new_deferred) = multi_winner_IRV_rule n (A - elected) p
    in (elected \<union> new_elected, rejected \<union> new_rejected, new_deferred))" *)


(*Modelo-este debería estar mal
fun multi_winner_IRV_rule :: "nat \<Rightarrow> 'a Electoral_Module" where
  "multi_winner_IRV_rule 0 A p = ({}, A, {})" 
| "multi_winner_IRV_rule (Suc n) A p = (
    let (winners, not_losers, losers) = IRV_rule A p;
        (new_winners, new_not_losers, new_losers) = multi_winner_IRV_rule n (A - winners) p
    in (winners \<union> new_winners, new_not_losers, losers \<union> new_losers))" *)





(*Just for the purpose of modelling the absolute majority rule ;) *)
fun abs_rule :: "'a Electoral_Module" where
  "abs_rule A p = elector absolute_max A p"

text \<open>
  These last functions have been developed for test purposes. 
  They are commented now for perfomance purposes. 
\<close>

(*
fun absolute' :: "'a Electoral_Module" where
"absolute' A p =
  ((min_eliminator abs_score) \<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d) A p"

fun abs_rule' :: "'a Electoral_Module" where
  "abs_rule' A p = iterelect absolute' A p"

fun IRV_rule2 :: "'a Electoral_Module" where
  "IRV_rule2 A p= (((absolute_max \<triangleright> min_eliminator IRV_score )\<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d)) A p"

fun IRV_rule3 :: "'a Electoral_Module" where
  "IRV_rule3 A p= (((abs_rule \<triangleright> min_eliminator IRV_score )\<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d)) A p"

fun mid_step:: "'a Electoral_Module" where
  "mid_step A p = (absolute_max \<triangleright> min_eliminator IRV_score) A p "
*)

end

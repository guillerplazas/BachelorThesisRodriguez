section \<open>IRV_Rule\<close>

theory IRV_Rule
  imports Pairwise_Majority_Rule
        "Compositional_Structures/Basic_Modules/abs_module"
          "Compositional_Structures/Defer_One_Loop_Composition"
           "independence_of_clones"
begin

fun IRV_score :: "'a Evaluation_Function" where
  "IRV_score x A p = win_count p x"

(*Aqui acaban definiciones de absolute*)

fun IRV_rule :: "'a Electoral_Module" where
  "IRV_rule A p= (((absolute_max \<triangleright> min_eliminator IRV_score )\<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d)\<triangleright> elect_module) A p"




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

lemma IRV_satisfies_independence_of_clones:
  shows "independence_of_clones IRV_rule"
unfolding independence_of_clones_def
proof (clarify)
  fix A :: "'a set" and p :: "'a Profile" and winner :: 'a
  assume IRV_winner: "IRV_rule A p = ({winner}, A-{winner}, {})"
  let ?clone = "clone_intro A p winner"
  obtain e' r' d' where rule_def: "IRV_rule (fst ?clone) (snd ?clone) = (e', r', d')" and singleton_e: "\<exists>x. e' = {x}"
    using prod_cases3 by blast
  moreover have "\<exists>w'. e' = {w'} \<and> (w' = winner \<or> clones_exist_in_A {w', winner} (snd ?clone))" 
  proof (cases "e' = {winner}")
    case True
    then show ?thesis by auto
  next
    case False
    then obtain new_winner where new_winner_def: "e' = {new_winner}" using singleton_e by auto
    have "new_winner = winner \<or> clones_exist_in_A {new_winner, winner} (snd ?clone)"
    proof (cases "new_winner = winner")
      case True
      then show ?thesis by simp
    next
      case False
      show ?thesis
      proof -
        have "clones_exist_in_A {new_winner, winner} (snd ?clone)"
        proof -
          have "new_winner \<in> fst ?clone" using new_winner_def rule_def by simp
          then have "new_winner \<in> A \<or> new_winner = winner" using clone_intro by metis
          then show ?thesis using False by auto
        qed
        then show ?thesis by simp
      qed
    qed
    then show ?thesis using new_winner_def by auto
  qed
  ultimately show "r' \<subseteq> A' \<and> (\<exists>w'. e' = {w'} \<and> (w' = winner \<or> clones_exist_in_A {w', winner} (snd ?clone)))"
    by auto
qed



(*Proof mas avanzada*)
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

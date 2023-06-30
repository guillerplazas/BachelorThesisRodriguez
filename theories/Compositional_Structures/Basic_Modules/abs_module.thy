section \<open>Plurality Module\<close>

theory abs_module
  imports 
 "Component_Types/Elimination_Module"
 "Component_Types/Social_Choice_Types/Profile"
 "Defer_Module"
 "Drop_Module"



begin


subsection \<open>Definition Eliminator\<close>



fun eliminate_least_score :: "'a Evaluation_Function \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a Electoral_Module" where
  "eliminate_least_score e r A p =
    (if A = {} then ({}, {}, {})
     else
        (if card A = 1 then defer_module A p  
        else
          let scores = {e x A p | x. x \<in> A};
              min_score = Min scores;
              candidates_with_min_score = {x \<in> A. e x A p = min_score}
          in
            if candidates_with_min_score = {} then ({}, {}, A)
            else 
              if card candidates_with_min_score = 1 then ({}, candidates_with_min_score, A-candidates_with_min_score)
              else
                let (_, to_eliminate, _) = drop_module 1 r candidates_with_min_score p
                in
                  if to_eliminate = {} then ({},{},A)
                  else ({}, to_eliminate, A - to_eliminate)))"

subsection \<open>Soundness Proofs \<close>

lemma eliminate_least_score_sound_for_empty_A:
  assumes "finite_profile A p" 
    and "A = {}"
  shows "well_formed A (eliminate_least_score e r A p)"
proof -
  from assms have "eliminate_least_score e r A p = ({}, {}, {})" by simp
  hence "({} \<union> {} \<union> {}) = A"
    by (simp add: assms(2))   
  have "disjoint3 ({}, {}, {})" by simp
  moreover have "set_equals_partition {} ({}, {}, {})" by simp
  ultimately show "well_formed A (eliminate_least_score e r A p)"
    unfolding well_formed.simps using assms(2) by simp
qed

lemma eliminate_least_score_sound_for_A_eq_1:
  assumes "finite_profile A p" 
    and "A \<noteq> {}"
    and "card A =1"
  shows "well_formed A (eliminate_least_score e r A p)"
proof -
  from assms obtain c where "A = {c}"
    by (auto simp: card_Suc_eq)

  have elim_res: "eliminate_least_score e r A p = ({}, {}, A)"
    using `A = {c}` assms(2) assms(3) by simp

  have "disjoint3 ({}, {}, A)" by simp
  moreover have "set_equals_partition A ({}, {}, A)" using `A = {c}` by simp
  ultimately show "well_formed A (eliminate_least_score e r A p)"
    unfolding well_formed.simps using elim_res by simp
qed

lemma eliminate_least_score_sound_for_cwms_empty:
  assumes "finite_profile A p" 
    and "A \<noteq> {}"
    and "card A \<noteq>1"
    and "{x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}={}"
  shows "well_formed A (eliminate_least_score e r A p)"
proof -
  have elim_res: "eliminate_least_score e r A p = ({}, {}, A)"
    using assms(4) by auto
  have "disjoint3 ({}, {}, A)" by simp
  moreover have "set_equals_partition A ({}, {}, A)" by simp
  ultimately show "well_formed A (eliminate_least_score e r A p)"
    unfolding well_formed.simps using elim_res by simp
qed

lemma eliminate_least_score_sound_for_cwms_one:
  assumes "finite_profile A p" 
    and "A \<noteq> {}"
    and "card A \<noteq>1"
    and "{x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}\<noteq>{}"
    and "card {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}=1"
  shows "well_formed A (eliminate_least_score e r A p)"
proof -
  let ?candidates_with_min_score = "{x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}"
  obtain e_set r_set d_set where 
    elim_result: "eliminate_least_score e r A p = (e_set, r_set, d_set)"
    using prod_cases3 by blast

  have "e_set = {}"
  proof -
    have "\<not>(\<forall>x. x \<in> A \<longrightarrow> e x A p \<noteq> Min {e x A p | x. x \<in> A})"
      using assms(4) by blast
    hence "eliminate_least_score e r A p = ({}, ?candidates_with_min_score, A - ?candidates_with_min_score)"
      by (smt (verit) Collect_cong assms(2) assms(3) assms(4) assms(5) eliminate_least_score.simps)
    thus "e_set = {}" using elim_result by simp
  qed
  
  have "r_set = ?candidates_with_min_score" 
    proof -
    have "fst (snd (eliminate_least_score e r A p)) = r_set"
      using elim_result by auto

    moreover have "fst (snd (eliminate_least_score e r A p)) = ?candidates_with_min_score"
    unfolding eliminate_least_score.simps
    using assms(4) assms(5)
    by (smt (verit) Collect_cong \<open>e_set = {}\<close> assms(1) assms(2) assms(3) calculation elim_result fst_conv prod.collapse snd_conv)

    ultimately show "r_set = ?candidates_with_min_score"
      by simp
  qed

  have "d_set = A - r_set" 
    proof -
    have "snd (snd (eliminate_least_score e r A p)) = A - ?candidates_with_min_score"
      using `card ?candidates_with_min_score = 1` `?candidates_with_min_score \<noteq> {}` `eliminate_least_score e r A p = (e_set, r_set, d_set)`
      unfolding eliminate_least_score.simps
      by (smt (verit, ccfv_SIG) assms(2) assms(3) snd_conv)

    moreover have "snd (snd (eliminate_least_score e r A p)) = d_set"
      using elim_result by auto
    ultimately show "d_set = A - r_set"
    using \<open>r_set = ?candidates_with_min_score\<close> by auto
  qed
  
  
  have partition_subsets: "e_set \<subseteq> A \<and> r_set \<subseteq> A \<and> d_set \<subseteq> A"
    using `e_set = {}` `r_set = ?candidates_with_min_score` `d_set = A - r_set` by auto
  have partition_inter_empty: "e_set \<inter> r_set = {} \<and> e_set \<inter> d_set = {} \<and> r_set \<inter> d_set = {}"
    using `e_set = {}` `d_set = A - r_set` by auto
  have partition_union_is_A: "e_set \<union> r_set \<union> d_set = A"
    using `e_set = {}` `d_set = A - r_set` `r_set = ?candidates_with_min_score` by auto
    

  show "well_formed A (eliminate_least_score e r A p)"
    using elim_result partition_inter_empty partition_union_is_A by auto
qed

lemma eliminate_least_score_sound_for_te_empty:
  assumes "finite_profile A p" 
    and "A \<noteq> {}"
    and "card A \<noteq>1"
    and "{x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}\<noteq>{}"
    and "card {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}\<noteq>1"
    and "\<exists>a b. drop_module 1 r {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} p = (a, {}, b)"
  shows "well_formed A (eliminate_least_score e r A p)"
proof-
  let ?candidates_with_min_score = "{x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}"
  obtain e_set r_set d_set where
    elim_result: "eliminate_least_score e r A p = (e_set, r_set, d_set)"
    using prod_cases3 by blast

  obtain a b where drop_module_res: "drop_module 1 r ?candidates_with_min_score p = (a, {}, b)"
    using assms(6) by auto  

 obtain some_var to_eliminate another_var where to_eliminate_def: "(some_var, to_eliminate, another_var) = drop_module 1 r ?candidates_with_min_score p"
   by auto

have "to_eliminate ={}"
      using drop_module_res to_eliminate_def by auto

then have "eliminate_least_score e r A p = ({}, {}, A)"
    using assms(2) assms(3) assms(4) assms(5) to_eliminate_def `to_eliminate = {}`
    by (simp add: Let_def)

     have "e_set = {}" using `eliminate_least_score e r A p = ({}, {}, A)`
       using elim_result by auto

 have "r_set = {}" using `eliminate_least_score e r A p = ({}, {}, A)`
   using elim_result by auto

 have "d_set = A" using `eliminate_least_score e r A p = ({}, {}, A)`
   using elim_result by auto
 
   show "well_formed A (eliminate_least_score e r A p)"
     using \<open>eliminate_least_score e r A p = ({}, {}, A)\<close> by auto

qed

lemma eliminate_least_score_sound_for_te_non_empty:
  assumes "finite_profile A p" 
    and "A \<noteq> {}"
    and "card A \<noteq>1"
    and "{x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}\<noteq>{}"
    and "card {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}\<noteq>1"
    and "\<exists>a b c . drop_module 1 r {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} p =(a, to_eliminate, b)"
    and "to_eliminate \<noteq>{}" 
  shows "well_formed A (eliminate_least_score e r A p)"
proof-
  let ?candidates_with_min_score = "{x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}"
  obtain e_set r_set d_set where
    elim_result: "eliminate_least_score e r A p = (e_set, r_set, d_set)"
    using prod_cases3 by blast

  obtain a to_eliminate b  where drop_module_res: "drop_module 1 r ?candidates_with_min_score p = (a,to_eliminate, b)"
    using assms(6) by auto


  then have "eliminate_least_score e r A p = ({}, to_eliminate, A - to_eliminate)"
    using assms(2) assms(3) assms(4) assms(5) drop_module_res
    by (simp add: Let_def)

 have "e_set = {}" using `eliminate_least_score e r A p =  ({}, to_eliminate, A - to_eliminate)`
       using elim_result by auto

 have "r_set = to_eliminate" using `eliminate_least_score e r A p =  ({}, to_eliminate, A - to_eliminate)`
   using elim_result by auto

 have "d_set = A-to_eliminate" using `eliminate_least_score e r A p = ({}, to_eliminate, A - to_eliminate)`
   using elim_result by auto

  have  "e_set \<subseteq> A"
    by (simp add: \<open>e_set = {}\<close>)

 have  "?candidates_with_min_score \<subseteq> A"
   by simp

    have "to_eliminate \<subseteq> ?candidates_with_min_score"
  proof -
    have "to_eliminate = {a \<in> ?candidates_with_min_score. card(above (limit ?candidates_with_min_score r) a) \<le> 1}"
      using drop_module_res by simp
    thus ?thesis by auto
  qed
    

   have  "to_eliminate \<subseteq> A" using `to_eliminate \<subseteq> ?candidates_with_min_score` `?candidates_with_min_score \<subseteq> A` drop_module_res
     by blast
   have "d_set \<subseteq> A"
     by (simp add: \<open>d_set = A - to_eliminate\<close>) 

    have partition_subsets: "e_set \<subseteq> A \<and> r_set \<subseteq> A \<and> d_set \<subseteq> A"
      by (simp add: \<open>d_set \<subseteq> A\<close> \<open>e_set \<subseteq> A\<close> \<open>r_set = to_eliminate\<close> \<open>to_eliminate \<subseteq> A\<close>)
   have partition_inter_empty: "e_set \<inter> r_set = {} \<and> e_set \<inter> d_set = {} \<and> r_set \<inter> d_set = {}"
    using `e_set = {}` `d_set = A - to_eliminate`
    by (simp add: \<open>r_set = to_eliminate\<close>)
  have partition_union_is_A: "e_set \<union> r_set \<union> d_set = A"
    using \<open>d_set = A - to_eliminate\<close> \<open>r_set = to_eliminate\<close> partition_subsets by auto

    
 show "well_formed A (eliminate_least_score e r A p)"
   using elim_result partition_inter_empty partition_union_is_A by fastforce
qed

theorem eliminate_least_score_soundness:
  assumes "finite_profile A p"
  shows "well_formed A (eliminate_least_score e r A p)"
proof (cases "A = {}")
  case True
  then show ?thesis
    using assms eliminate_least_score_sound_for_empty_A by simp
next
  case False
  then show ?thesis
  proof (cases "card A = 1")
    case True
    then show ?thesis
      using assms eliminate_least_score_sound_for_A_eq_1 by simp
  next
    case False
    then show ?thesis
    proof (cases "{x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} = {}")
      case True
      then show ?thesis
        using assms eliminate_least_score_sound_for_cwms_empty by simp
    next
      case False
      then show ?thesis
      proof (cases "card {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} = 1")
        case True
        then show ?thesis
          using assms eliminate_least_score_sound_for_cwms_one
          by (smt (verit) Collect_cong False eliminate_least_score_sound_for_A_eq_1 empty_def mem_Collect_eq)
      next
        case False
        then show ?thesis
        proof (cases "\<exists>a b. drop_module 1 r {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} p = (a, {}, b)")
          case True
          then show ?thesis
            using assms `A \<noteq> {}` `card A \<noteq> 1` `{x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} \<noteq> {}` `card {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} \<noteq> 1` eliminate_least_score_sound_for_te_empty
            by blast
        next
          case False
         then obtain a b c where drop_mod_res: "drop_module 1 r {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} p = (a, c, b)"
  by (meson assms drop_module.elims)
then have "c \<noteq> {}"
  using False by auto
  then show ?thesis
    sorry
        qed
      qed
    qed
  qed
qed





subsection \<open>Non-Electing Proofs\<close>


subsection \<open>Cardinality Eliminations\<close>

lemma eliminate_least_score_card_for_empty_A:
  assumes "finite_profile A p" 
    and "A = {}"
  shows "card (reject_r (eliminate_least_score e r A p))< 2"
proof -
  from assms have "eliminate_least_score e r A p = ({}, {}, {})" by simp
  hence "({} \<union> {} \<union> {}) = A"
    by (simp add: assms(2))   
  show "card (reject_r (eliminate_least_score e r A p))< 2"
    using \<open>eliminate_least_score e r A p = ({}, {}, {})\<close> by auto
qed

lemma eliminate_least_score_card_for_A_eq_1:
  assumes "finite_profile A p" 
    and "A \<noteq> {}"
    and "card A =1"
  shows "card (reject_r (eliminate_least_score e r A p))< 2"
proof -
  from assms obtain c where "A = {c}"
    by (auto simp: card_Suc_eq)

  have elim_res: "eliminate_least_score e r A p = ({}, {}, A)"
    using `A = {c}` assms(2) assms(3) by simp
  show "card (reject_r (eliminate_least_score e r A p))< 2"
    by (simp add: assms(3))
qed




lemma eliminate_least_score_card_for_cwms_empty:
  assumes "finite_profile A p" 
    and "A \<noteq> {}"
    and "card A \<noteq>1"
    and "{x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}={}"
  shows"card (reject_r (eliminate_least_score e r A p))< 2"
proof -
  have elim_res: "eliminate_least_score e r A p = ({}, {}, A)"
    using assms(4) by auto
  have "disjoint3 ({}, {}, A)" by simp
  show "card (reject_r (eliminate_least_score e r A p))< 2"
    using elim_res by auto
qed

lemma eliminate_least_score_card_for_cwms_one:
  assumes "finite_profile A p" 
    and "A \<noteq> {}"
    and "card A \<noteq>1"
    and "{x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}\<noteq>{}"
    and "card {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}=1"
  shows "card (reject_r (eliminate_least_score e r A p))< 2"
proof -
  let ?candidates_with_min_score = "{x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}"
  obtain e_set r_set d_set where 
    elim_result: "eliminate_least_score e r A p = (e_set, r_set, d_set)"
    using prod_cases3 by blast

  have "e_set = {}"
  proof -
    have "\<not>(\<forall>x. x \<in> A \<longrightarrow> e x A p \<noteq> Min {e x A p | x. x \<in> A})"
      using assms(4) by blast
    hence "eliminate_least_score e r A p = ({}, ?candidates_with_min_score, A - ?candidates_with_min_score)"
      by (smt (verit) Collect_cong assms(2) assms(3) assms(4) assms(5) eliminate_least_score.simps)
    thus "e_set = {}" using elim_result by simp
  qed
  
  have "r_set = ?candidates_with_min_score" 
    proof -
    have "fst (snd (eliminate_least_score e r A p)) = r_set"
      using elim_result by auto

    moreover have "fst (snd (eliminate_least_score e r A p)) = ?candidates_with_min_score"
    unfolding eliminate_least_score.simps
    using assms(4) assms(5)
    by (smt (verit) Collect_cong \<open>e_set = {}\<close> assms(1) assms(2) assms(3) calculation elim_result fst_conv prod.collapse snd_conv)

    ultimately show "r_set = ?candidates_with_min_score"
      by simp
  qed

  have "card (?candidates_with_min_score)<2"
    by (simp add: assms(5))

  have "card (r_set) <2" using `card (?candidates_with_min_score)<2` `r_set = ?candidates_with_min_score`
    by blast

  have "d_set = A - r_set" 
    proof -
    have "snd (snd (eliminate_least_score e r A p)) = A - ?candidates_with_min_score"
      using `card ?candidates_with_min_score = 1` `?candidates_with_min_score \<noteq> {}` `eliminate_least_score e r A p = (e_set, r_set, d_set)`
      unfolding eliminate_least_score.simps
      by (smt (verit, ccfv_SIG) assms(2) assms(3) snd_conv)

    moreover have "snd (snd (eliminate_least_score e r A p)) = d_set"
      using elim_result by auto
    ultimately show "d_set = A - r_set"
    using \<open>r_set = ?candidates_with_min_score\<close> by auto
  qed
    show "card (reject_r (eliminate_least_score e r A p))< 2"
      using \<open>card r_set < 2\<close> elim_result by fastforce
  qed

lemma eliminate_least_score_card_for_te_empty:
  assumes "finite_profile A p" 
    and "A \<noteq> {}"
    and "card A \<noteq>1"
    and "{x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}\<noteq>{}"
    and "card {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}\<noteq>1"
    and "\<exists>a b. drop_module 1 r {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} p = (a, {}, b)"
  shows "card (reject_r (eliminate_least_score e r A p))< 2"
proof-
  let ?candidates_with_min_score = "{x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}"
  obtain e_set r_set d_set where
    elim_result: "eliminate_least_score e r A p = (e_set, r_set, d_set)"
    using prod_cases3 by blast

  obtain a b where drop_module_res: "drop_module 1 r ?candidates_with_min_score p = (a, {}, b)"
    using assms(6) by auto  

 obtain some_var to_eliminate another_var where to_eliminate_def: "(some_var, to_eliminate, another_var) = drop_module 1 r ?candidates_with_min_score p"
   by auto

have "to_eliminate ={}"
      using drop_module_res to_eliminate_def by auto

then have "eliminate_least_score e r A p = ({}, {}, A)"
    using assms(2) assms(3) assms(4) assms(5) to_eliminate_def `to_eliminate = {}`
    by (simp add: Let_def)

     have "e_set = {}" using `eliminate_least_score e r A p = ({}, {}, A)`
       using elim_result by auto

 have "r_set = {}" using `eliminate_least_score e r A p = ({}, {}, A)`
   using elim_result by auto

 have "d_set = A" using `eliminate_least_score e r A p = ({}, {}, A)`
   using elim_result by auto
 
     show "card (reject_r (eliminate_least_score e r A p))< 2"
       using \<open>r_set = {}\<close> elim_result by force
   
   qed

lemma eliminate_least_score_card_for_te_non_empty:
  assumes "finite_profile A p" 
    and "A \<noteq> {}"
    and "card A \<noteq>1"
    and "{x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}\<noteq>{}"
    and "card {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}\<noteq>1"
    and "\<exists>a b c . drop_module 1 r {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} p =(a, to_eliminate, b)"
    and "to_eliminate \<noteq>{}" 
  shows "card (reject_r (eliminate_least_score e r A p))< 2"
proof-
  let ?candidates_with_min_score = "{x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}"
  obtain e_set r_set d_set where
    elim_result: "eliminate_least_score e r A p = (e_set, r_set, d_set)"
    using prod_cases3 by blast

  obtain a to_eliminate b  where drop_module_res: "drop_module 1 r ?candidates_with_min_score p = (a,to_eliminate, b)"
    using assms(6) by auto

  have "card (to_eliminate)<2"

  then have "eliminate_least_score e r A p = ({}, to_eliminate, A - to_eliminate)"
    using assms(2) assms(3) assms(4) assms(5) drop_module_res
    by (simp add: Let_def)

 have "e_set = {}" using `eliminate_least_score e r A p =  ({}, to_eliminate, A - to_eliminate)`
       using elim_result by auto

 have "r_set = to_eliminate" using `eliminate_least_score e r A p =  ({}, to_eliminate, A - to_eliminate)`
   using elim_result by auto

 have "d_set = A-to_eliminate" using `eliminate_least_score e r A p = ({}, to_eliminate, A - to_eliminate)`
   using elim_result by auto

  have  "e_set \<subseteq> A"
    by (simp add: \<open>e_set = {}\<close>)

 have  "?candidates_with_min_score \<subseteq> A"
   by simp

    have "to_eliminate \<subseteq> ?candidates_with_min_score"
  proof -
    have "to_eliminate = {a \<in> ?candidates_with_min_score. card(above (limit ?candidates_with_min_score r) a) \<le> 1}"
      using drop_module_res by simp
    thus ?thesis by auto
  qed
     show "card (reject_r (eliminate_least_score e r A p))< 2"

   have  "to_eliminate \<subseteq> A" using `to_eliminate \<subseteq> ?candidates_with_min_score` `?candidates_with_min_score \<subseteq> A` drop_module_res
     by blast
   have "d_set \<subseteq> A"
     by (simp add: \<open>d_set = A - to_eliminate\<close>) 

    have partition_subsets: "e_set \<subseteq> A \<and> r_set \<subseteq> A \<and> d_set \<subseteq> A"
      by (simp add: \<open>d_set \<subseteq> A\<close> \<open>e_set \<subseteq> A\<close> \<open>r_set = to_eliminate\<close> \<open>to_eliminate \<subseteq> A\<close>)
   have partition_inter_empty: "e_set \<inter> r_set = {} \<and> e_set \<inter> d_set = {} \<and> r_set \<inter> d_set = {}"
    using `e_set = {}` `d_set = A - to_eliminate`
    by (simp add: \<open>r_set = to_eliminate\<close>)
  have partition_union_is_A: "e_set \<union> r_set \<union> d_set = A"
    using \<open>d_set = A - to_eliminate\<close> \<open>r_set = to_eliminate\<close> partition_subsets by auto

    
 show "well_formed A (eliminate_least_score e r A p)"
   using elim_result partition_inter_empty partition_union_is_A by fastforce
qed



(*Some functions might need reordering*)
subsection \<open>Functions absolute module\<close>

fun abs_winner :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "abs_winner A p w =
  (finite_profile A p \<and> w \<in> A \<and> (has_majority p w))"

fun abs_score :: "'a Evaluation_Function" where
  "abs_score x A p =
    (if (abs_winner A p x) then 1 else 0)"

fun abs_existence:: "'a set \<Rightarrow> 'a Profile  \<Rightarrow> bool" where
  "abs_existence A p = (\<exists> x \<in> A . abs_winner A p x)"

(*default*)
fun absolute_max:: "'a Electoral_Module" where
  "absolute_max A p = (if (abs_existence A p) then ( max_eliminator abs_score A p) else defer_module A p)"

(*Garbage*)
(*
fun absolute_min:: "'a Electoral_Module" where
  "absolute_min A p = min_eliminator abs_score A p"
*)


end
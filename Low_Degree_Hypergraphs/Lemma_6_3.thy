
theory Lemma_6_3
  imports Main Lemma_6_3_Extra Vector "HOL-Probability.Probability_Mass_Function" "HOL-Probability.Product_PMF"
begin

lemma lemma_6_3:
  assumes "0 \<le> p" and p_less_1: "p < 1" and "finite V" and "U \<subseteq> V" and "U' \<subseteq> V" and 
          card_U: "card U = d" and card_U': "card U' = d" and card_U_Int_U': "card (U \<inter> U') = r" and 
          fin_x: "Vector.finite x" and vect_x: "vector x" and rng_x: "range x \<subseteq> {0, 1}" and len_x: "length x = n"
  shows "measure_pmf.prob (vector_of (random_subset V p) n) {Ss. map_vector (intersect U) Ss = x \<and> map_vector (intersect U') Ss = x \<and> (\<forall>S\<in>range Ss. S \<sqsubseteq> V)} = ((1 - p) ^ ((2 * d - r) * n)) * ((p * r)/(1-p) + ((p * (d-r))/(1-p))^2)^(count x 1)"
proof -
  note finite_U = finite_subset[OF assms(4) assms(3)]
  note finite_U' = finite_subset[OF assms(5) assms(3)]
  have bernoulli_True: "pmf (bernoulli_pmf p) True = p" and bernoulli_False: "pmf (bernoulli_pmf p) False = (1 - p)" using pmf_bernoulli_True pmf_bernoulli_False assms(1,2) by simp+

  have Pi_set_vector: "{Ss. map_vector (intersect U) Ss = x \<and> map_vector (intersect U') Ss = x \<and> (\<forall>S\<in>range Ss. S \<sqsubseteq> V)} = (PiE_dflt {i. i<n} None (\<lambda>i. {S. map_option (intersect U) S = x i \<and> map_option (intersect U') S = x i \<and> (case S of Some s \<Rightarrow> s \<sqsubseteq> V | None \<Rightarrow> True)}))" (is "?lhs = ?rhs")
  proof
    show "?lhs \<subseteq> ?rhs"
    proof 
      fix Ss assume asm: "Ss \<in> ?lhs" hence a0: "map_vector (intersect U) Ss = x" and a1: "map_vector (intersect U') Ss = x" and a2: "(\<forall>S\<in>range Ss. S \<sqsubseteq> V)" by blast+
      from a0 have a3: "\<forall>i<n. map_option (intersect U) (Ss i) = x i" by fastforce
      from a1 have a4: "\<forall>i<n. map_option (intersect U') (Ss i) = x i" by fastforce

      from map_vector_vector vect_x a0 have a5: "vector Ss" by auto
      from map_vector_fin fin_x a0 have a6: "Vector.finite Ss" by auto 
      from map_vector_len len_x a0 have a7: "length Ss = n" by auto
      from a5 a6 a7 have a8: "\<forall>i\<ge>n. Ss i = None" using ge_len_is_None by blast
      from a2 vector_Ball_range have "\<forall>i. (case (Ss i) of Some s \<Rightarrow> s \<sqsubseteq> V | None \<Rightarrow> True)" by fastforce
      with a3 a4 a8 show "Ss \<in> ?rhs" unfolding PiE_dflt_def by simp
    qed
  next
    show "?rhs \<subseteq> ?lhs"
    proof
      fix Ss assume "Ss \<in> ?rhs" 
      hence a0: "\<forall>i<n. map_option (intersect U) (Ss i) = x i" and a1: "\<forall>i<n. map_option (intersect U') (Ss i) = x i" and a2: "\<forall>i\<ge>n. Ss i = None" and a3: "\<forall>i<n. (case (Ss i) of Some s \<Rightarrow> s \<sqsubseteq> V | None \<Rightarrow> True)" unfolding PiE_dflt_def by auto
      from a3 vector_Ball_range[of "Ss" "\<lambda>S. subsetof S V"] have "(\<forall>S\<in>range Ss. S \<sqsubseteq> V)" by (metis a2 linorder_not_le option.case_eq_if)
      with map_vector_inverse[OF vect_x fin_x len_x a0 a2] map_vector_inverse[OF vect_x fin_x len_x a1 a2] show "Ss \<in> ?lhs" by simp
    qed
  qed
  
  have Pi_set_x_i_is_0: "{S. card {u\<in>U. S u} = 0 \<and> card {u\<in>U'. S u} = 0 \<and> S \<sqsubseteq> V} = PiE_dflt V False (\<lambda>v. if v \<in> (U \<union> U') then {False} else UNIV)" (is "?lhs = ?rhs")
  proof
    show "?lhs \<subseteq> ?rhs"
    proof
      fix S assume "S \<in> ?lhs" hence a0: "card {u\<in>U. S u} = 0" and a1: "card {u\<in>U'. S u} = 0" and a2: "S \<sqsubseteq> V" by blast+
      from a0 a1 finite_UnI[OF finite_U finite_U'] have a3: "\<forall>v\<in>V. v \<in> (U \<union> U') \<longrightarrow> \<not>S v" by auto
      from a2 have "\<forall>v\<in>UNIV - V. \<not>S v" by fastforce
      with a3 show "S \<in> ?rhs" unfolding PiE_dflt_def by force
    qed
  next
    show "?rhs \<subseteq> ?lhs"
    proof
      fix S assume "S \<in> ?rhs" hence a0: "\<forall>v\<in>V. v \<in> (U \<union> U') \<longrightarrow> \<not>S v" and a1: "\<forall>v\<in>UNIV - V. \<not>S v" unfolding PiE_dflt_def by fastforce+
      from a0 assms(4,5) finite_U finite_U' have a2: "card {u\<in>U. S u} = 0" and a3: "card {u\<in>U'. S u} = 0" by auto
      from a1 a2 a3 show "S \<in> ?lhs" by auto
    qed
  qed

  have inner: "i < n \<Longrightarrow> measure_pmf.prob (random_subset V p) {S. Some (intersect U S) = x i \<and> Some (intersect U' S) = x i \<and> S \<sqsubseteq> V} 
        = (1 - p) ^ (2 * d - r) * ((p * r)/(1-p) + ((p * (d-r))/(1-p))^2)^(the (x i))" for i
  proof (cases "x i")
    case None
    assume "i < n" hence "i < length x" using len_x by blast
    from less_len_is_Some[OF vect_x fin_x this] None show ?thesis ..
  next
    case (Some a)
    assume "i < n"
    have subset_U_U': "U \<union> U' \<subseteq> V" using assms(4,5) by blast
    have bernoulli_prob_space: "space (measure_pmf (bernoulli_pmf p)) = {True, False}" by force
    have card_U_Un_U': "card (U \<union> U') = 2 * d - r" by (metis assms(6,7,8) add_diff_cancel_right' card_Un_Int finite_U finite_U' mult_2)
    have card_diffU: "card (U - U') = d - r" by (simp add: assms(6) card_U_Int_U' card_Diff_subset_Int finite_U')
    have card_diffU': "card (U' - U) = d - r" by (simp add: assms(7) card_U_Int_U' card_Diff_subset_Int finite_U' inf_commute)
    show ?thesis
    proof (cases a)
      case 0
      from 0 have "measure_pmf.prob (random_subset V p) {S. Some (intersect U S) = x i \<and> Some (intersect U' S) = x i \<and> S \<sqsubseteq> V}
      =  measure_pmf.prob (random_subset V p) {S. card {u\<in>U. S u} = 0 \<and> card {u\<in>U'. S u} = 0 \<and> S \<sqsubseteq> V}" using Some by force
      also have "... = measure_pmf.prob (Pi_pmf V False (\<lambda>_. bernoulli_pmf p)) {S. card {u\<in>U. S u} = 0 \<and> card {u\<in>U'. S u} = 0 \<and> S \<sqsubseteq> V}" using Some by simp
      also have "... = measure_pmf.prob (Pi_pmf V False (\<lambda>_. bernoulli_pmf p)) (PiE_dflt V False (\<lambda>v. if v \<in> (U \<union> U') then {False} else UNIV))" by (simp only: Pi_set_x_i_is_0)
      also have "... = (\<Prod>v\<in>(U \<union> U'). pmf (bernoulli_pmf p) False)" by (simp only: measure_Pi_pmf_PiE_dflt_subset[OF subset_U_U' assms(3)] measure_pmf_single)
      also have "... = (1 - p) ^ (2 * d - r)" using bernoulli_False card_U_Un_U' by fastforce
      finally show ?thesis by (simp add: 0 Some)
    next
      case (Suc nat) hence a_noteq_0: "a \<noteq> 0" by fast
      with vector_range_Some[of x, OF Some] rng_x have a_is_1: "a = 1" by blast
      show ?thesis
      proof (cases "2 > 2 * d - r")
        case _: True
        hence "2 * d - r = 0 \<or> 2 * d - r = 1" by force
        thus ?thesis 
        proof
          assume "2 * d - r = 0"
          with card_U_Un_U' have "(U \<union> U') = {}" by (simp add: finite_subset[OF assms(4) assms(3)] finite_subset[OF assms(5) assms(3)])
          thus ?thesis
          proof
            assume "U = {} \<and> U' = {}" hence U_empty: "U = {}" and U'_empty: "U' = {}" by blast+
            hence d_is_0: "d = 0" and r_is_0: "r = 0" using assms(6, 8) by simp+
            have "measure_pmf.prob (random_subset V p) {S. Some (intersect U S) = x i \<and> Some (intersect U' S) = x i \<and> S \<sqsubseteq> V}
                           = measure_pmf.prob (Pi_pmf V False (\<lambda>_. bernoulli_pmf p)) {S. card {u\<in>U. S u} = 1 \<and> card {u\<in>U'. S u} = 1 \<and> S \<sqsubseteq> V}" by (simp add: a_is_1 Some)
            also have "... = measure_pmf.prob (Pi_pmf V False (\<lambda>_. bernoulli_pmf p)) {S. card {u\<in>{}. S u} = 1 \<and> card {u\<in>{}. S u} = 1 \<and> S \<sqsubseteq> V}" using U_empty U'_empty by fast
            also have "... = measure_pmf.prob (Pi_pmf V False (\<lambda>_. bernoulli_pmf p)) {}" by simp
            also have "... = 0" using measure_empty by blast
            finally show ?thesis using d_is_0 r_is_0 a_is_1 Some by fastforce
          qed
        next
          assume "2 * d - r = 1"
          with card_U_Un_U' have "card (U \<union> U') = 1" by argo
          hence "\<exists>v. U \<union> U' = {v}" by (meson card_1_singletonE) then obtain v where "U \<union> U' = {v}" by force
          with card_U card_U' Un_singleton_iff[of U U' v] have U_is_v: "U = {v}" and U'_is_v: "U' = {v}" by fastforce+
          with card_U card_U' card_U_Int_U' have d_is_1: "d = 1" and r_is_1: "r = 1" by simp+
          have v_subseteq_V: "{v} \<subseteq> V" using U_is_v assms(4) by blast

          have Pi_set_inner_exception: "{S. card {u\<in>{v}. S u} = 1 \<and> S \<sqsubseteq> V} = (PiE_dflt V False (\<lambda>u. if u \<in> {v} then {True} else UNIV))" (is "?lhs = ?rhs")
          proof
            show "?lhs \<subseteq> ?rhs"
            proof
              fix S assume "S \<in> ?lhs" hence a0: "card {u\<in>{v}. S u} = 1" and a1: "S \<sqsubseteq> V" by blast+
              from a0 have a2: "S v" by (metis (no_types, lifting) a_noteq_0 a_is_1 card_eq_0_iff empty_Collect_eq singletonD)
              from a1 have "\<forall>v\<in>UNIV - V. \<not>S v" by fastforce
              with a2 show "S \<in> ?rhs" unfolding PiE_dflt_def by simp
            qed
          next
            show "?rhs \<subseteq> ?lhs"
            proof
              fix S assume "S \<in> ?rhs" 
              with v_subseteq_V have a0: "S v" and a1: "\<forall>v\<in>UNIV - V. \<not>S v" unfolding PiE_dflt_def by fastforce+
              from a0 have "{u \<in> {v}. S u} = {v}" by blast
              hence "card {u\<in>{v}. S u} = 1" by simp
              with a1 show "S \<in> ?lhs" by auto
            qed
          qed
            
          from a_is_1 have "measure_pmf.prob (random_subset V p) {S. Some (intersect U S) = x i \<and> Some (intersect U' S) = x i \<and> S \<sqsubseteq> V}
                           = measure_pmf.prob (Pi_pmf V False (\<lambda>_. bernoulli_pmf p)) {S. card {u\<in>{v}. S u} = 1 \<and> S \<sqsubseteq> V}" using U_is_v U'_is_v Some by simp
          also have "... = measure_pmf.prob (Pi_pmf V False (\<lambda>_. bernoulli_pmf p)) (PiE_dflt V False (\<lambda>u. if u \<in> {v} then {True} else UNIV))" by (simp only: Pi_set_inner_exception)
          also have "... = pmf (bernoulli_pmf p) True" by (auto simp only: measure_Pi_pmf_PiE_dflt_subset[OF v_subseteq_V assms(3)] measure_pmf_single prod_constant, simp)
          also have "... = p" using bernoulli_True by fastforce
          finally show ?thesis using d_is_1 r_is_1 a_is_1 Some p_less_1 by force
        qed
      next
        case _: False hence exponent_is_nat1: "1 \<le> 2 * d - r" and exponent_is_nat2: "2 \<le> 2 * d - r" by fastforce+

        let ?E1 = "{S. card {u\<in>(U \<inter> U'). S u} = 1 \<and> card {u\<in>(U \<union> U'). S u} = 1 \<and> S \<sqsubseteq> V}"
        let ?E2 = "{S. card {u\<in>(U - U'). S u} = 1 \<and> card {u\<in>(U' - U). S u} = 1 \<and> card {u\<in>(U \<union> U'). S u} = 2 \<and> S \<sqsubseteq> V}"
        have two_cases: "{S. card {u\<in>U. S u} = 1 \<and> card {u\<in>U'. S u} = 1 \<and> S \<sqsubseteq> V} = ?E1 \<union> ?E2" (is "?lhs = ?E1 \<union> ?E2")
        proof
          show "?lhs \<subseteq> ?E1 \<union> ?E2"
          proof
            fix S assume "S \<in> ?lhs" hence asm1: "card {u\<in>U. S u} = 1" and asm2: "card {u\<in>U'. S u} = 1" and asm3: "S \<sqsubseteq> V" by blast+
            from asm1 have "\<exists>v. {u\<in>U. S u} = {v}" by (meson card_1_singletonE) then obtain u where u_is: "{u\<in>U. S u} = {u}" by blast
            from asm2 have "\<exists>v. {u\<in>U'. S u} = {v}" by (meson card_1_singletonE) then obtain u' where u'_is: "{u\<in>U'. S u} = {u'}" by blast
            show "S \<in> ?E1 \<union> ?E2"
            proof (simp only: Un_commute[of ?E1 ?E2], standard)
              assume "S \<notin> ?E1" with asm3 have card_argument: "card {u\<in>(U \<inter> U'). S u} \<noteq> 1 \<or> card {u\<in>(U \<union> U'). S u} \<noteq> 1" by blast
              from u_is u'_is have "{u \<in> U \<inter> U'. S u} = {u} \<inter> {u'}" and "{u \<in> U \<union> U'. S u} = {u} \<union> {u'}" by blast+
              with card_argument have u_noteq_u': "u \<noteq> u'" by fastforce
              from u_is u'_is u_noteq_u' have a0: "{u\<in>(U - U'). S u} = {u}" by blast
              from u'_is u_is u_noteq_u'[symmetric] have a1: "{u\<in>(U' - U). S u} = {u'}" by blast
              from u_is u'_is u_noteq_u' have a2: "{u\<in>(U \<union> U'). S u} = {u, u'}" by blast
              from u_noteq_u' show "S \<in> ?E2" by (auto simp only: a0 a1 a2 asm3, simp+)
            qed
          qed
        next
          show "?E1 \<union> ?E2 \<subseteq> ?lhs"
          proof
            fix S assume "S \<in> ?E1 \<union> ?E2" hence asm1: "(card {u \<in> U \<inter> U'. S u} = 1 \<and> card {u \<in> U \<union> U'. S u} = 1) \<or> (card {u \<in> U - U'. S u} = 1 \<and> card {u \<in> U' - U. S u} = 1 \<and> card {u \<in> U \<union> U'. S u} = 2)" and asm2: "S \<sqsubseteq> V" by blast+
            from asm1 show "S \<in> ?lhs"
            proof
              assume asm: "card {u \<in> U \<inter> U'. S u} = 1 \<and> card {u \<in> U \<union> U'. S u} = 1"
              from asm have "\<exists>v. {u \<in> U \<inter> U'. S u} = {v}" by (meson card_1_singletonE) then obtain u where a0: "{u \<in> U \<inter> U'. S u} = {u}" by blast
              from asm have "\<exists>v. {u \<in> U \<union> U'. S u} = {v}" by (meson card_1_singletonE) then obtain u' where a1: "{u \<in> U \<union> U'. S u} = {u'}" by blast
              from a0 a1 have u_eq_u': "u = u'" by blast
              with a0 a1 have a2: "{u\<in>U. S u} = {u}" and a3: "{u\<in>U'. S u} = {u}" by blast+
              show "S \<in> ?lhs" by (auto simp only: a2 a3 asm2, simp+)
            next
              assume asm: "(card {u \<in> U - U'. S u} = 1 \<and> card {u \<in> U' - U. S u} = 1 \<and> card {u \<in> U \<union> U'. S u} = 2)" hence card_2: "card {u \<in> U \<union> U'. S u} = 2" by blast
              from asm have "\<exists>v. {u \<in> U - U'. S u} = {v}" by (meson card_1_singletonE) then obtain u where a0: "{u \<in> U - U'. S u} = {u}" by blast
              from asm have "\<exists>v. {u \<in> U' - U. S u} = {v}" by (meson card_1_singletonE) then obtain u' where a1: "{u \<in> U' - U. S u} = {u'}" by blast
              from a0 a1 have u_noteq_u': "u \<noteq> u'" by blast
              from a0 a1 have "{u, u'} \<subseteq> {u \<in> U \<union> U'. S u}" by blast
              from card_subset_eq[OF _ this] u_noteq_u' card_2 finite_UnI[OF finite_U finite_U'] have a2: "{u, u'} = {u \<in> U \<union> U'. S u}" by auto
              with a0 a1 a2 have a3: "{u \<in> U. S u} = {u}" and a4: "{u \<in> U'. S u} = {u'}" by blast+
              show "S \<in> ?lhs" by (auto simp only: a3 a4 asm2, simp+)
            qed
          qed
        qed
        have dsjnt_cases: "?E1 \<inter> ?E2 = {}" by auto

        have Pi_set_E1: "u\<in>U \<inter> U' \<Longrightarrow> {S. S u \<and> card {u'\<in>(U \<union> U'). S u'} = 1 \<and> S \<sqsubseteq> V} = PiE_dflt V False (\<lambda>v. (if v \<in> (U \<union> U') then {v = u} else UNIV))" (is "?asm \<Longrightarrow> ?lhs = ?rhs") for u 
        proof
          assume asm: ?asm
          hence u_in_Un: "u \<in> (U \<union> U')" by blast
          show "?lhs \<subseteq> ?rhs"
          proof
            fix S assume "S \<in> ?lhs" hence a0: "S u \<and> card {u'\<in>(U \<union> U'). S u'} = 1" and a1: "S \<sqsubseteq> V" by blast+
            from a0 u_in_Un have a2: "{u'\<in>(U \<union> U'). S u'} = {u}" by (metis (no_types, lifting) card_1_singletonE mem_Collect_eq singleton_iff)
            from a2 have a3: "\<forall>v\<in>V. (v \<in> (U \<union> U')) \<longrightarrow> S v = (v = u)" by blast
            from a1 have "\<forall>v\<in>UNIV - V. \<not>S v" by fastforce
            with a3 show "S \<in> ?rhs" unfolding PiE_dflt_def by simp
          qed
        next
          assume asm: ?asm
          hence u_in_Un: "u \<in> (U \<union> U')" by blast
          show "?rhs \<subseteq> ?lhs"
          proof
            fix S assume "S \<in> ?rhs" hence a0: "\<forall>v\<in>V. (v \<in> (U \<union> U')) \<longrightarrow> S v = (v = u)" and a1: "\<forall>v\<in>UNIV - V. \<not>S v" unfolding PiE_dflt_def by fastforce+
            from assms(4,5) have a2: "(U \<union> U') \<subseteq> V" by simp
            from a0 a2 u_in_Un have "{u'\<in>(U \<union> U'). S u'} = {u}" by blast
            with a1 show "S \<in> ?lhs" by auto
          qed
        qed
  
        have case_1: "measure_pmf.prob (Pi_pmf V False (\<lambda>_. bernoulli_pmf p)) ?E1 = card (U \<inter> U') * p * (1 - p) ^ (card (U \<union> U') - 1)" (is "?lhs = ?rhs")
        proof -
          have E1_is: "?E1 = (\<Union>u\<in>U \<inter> U'. {S. S u \<and> card {u\<in>(U \<union> U'). S u} = 1 \<and> S \<sqsubseteq> V})" (is "?lhs1 = ?rhs1")
          proof
            show "?lhs1 \<subseteq> ?rhs1"
            proof
              fix S assume "S \<in> ?lhs1" hence a: "card {u\<in>(U \<inter> U'). S u} = 1" and b: "card {u\<in>(U \<union> U'). S u} = 1" and c: "S \<sqsubseteq> V" by blast+
              from a have "\<exists>u \<in> U \<inter> U'. S u" by (metis (no_types, lifting) a_is_1 Collect_empty_eq \<open>a \<noteq> 0\<close> card.empty)
              with b c show "S \<in> ?rhs1" by blast
            qed
          next
            show "?rhs1 \<subseteq> ?lhs1"
            proof
              fix S assume "S \<in> ?rhs1" then obtain u where a: "u \<in> U \<inter> U'" and b: "S u" and c: "card {u\<in>(U \<union> U'). S u} = 1" and d: "S \<sqsubseteq> V" by blast+
              hence subset_1: "{u \<in> U \<inter> U'. S u} \<subseteq> {u \<in> U \<union> U'. S u}" by blast
              from card_mono[OF _ this] c have card_less_than_1: "card {u \<in> U \<inter> U'. S u} \<le> 1" by fastforce
  
              from finite_subset[OF subset_1] c have set_is_finite: "finite {u \<in> U \<inter> U'. S u}" by fastforce
              
              from a b have subset_2: "{u} \<subseteq> {u \<in> U \<inter> U'. S u}" by blast
              from card_mono[OF set_is_finite this] card_less_than_1 have "card {u \<in> U \<inter> U'. S u} = 1" by simp
              with c d show "S \<in> ?lhs1" by blast
            qed
          qed

          have p1: "finite (U \<inter> U')" using finite_U finite_U' by simp
          have p2: "(\<lambda>x. {S. S x \<and> card {u\<in>(U \<union> U'). S u} = 1 \<and> S \<sqsubseteq> V}) ` (U \<inter> U') \<subseteq> measure_pmf.events (Pi_pmf V False (\<lambda>_. bernoulli_pmf p))" by force
          have p3: "disjoint_family_on (\<lambda>x. {S. S x \<and> card {u\<in>(U \<union> U'). S u} = 1 \<and> S \<sqsubseteq> V}) (U \<inter> U')" unfolding disjoint_family_on_def
          proof (standard, standard, standard, standard, standard)
            fix m n S
            assume a1: "m \<in> U \<inter> U'" and a2: "n \<in> U \<inter> U'" and a3: "m \<noteq> n" and a4: "S \<in> {S. S m \<and> card {u \<in> U \<union> U'. S u} = 1 \<and> S \<sqsubseteq> V} \<inter> {S. S n \<and> card {u \<in> U \<union> U'. S u} = 1 \<and> S \<sqsubseteq> V}"
            from a4 have a5: "S m" and a6: "S n" and a7: "card {u \<in> U \<union> U'. S u} = 1" by blast+
            from a1 a2 a5 a6 have a8: "{n, m} \<subseteq> {u \<in> U \<union> U'. S u}" by blast
            from a3 have a9: "card {n, m} = 2" by auto
            have "finite {u \<in> U \<union> U'. S u}" by (simp add: finite_U finite_U')
            from card_mono[OF this a8] a9 a7 show "S \<in> {}" by linarith
          qed (blast)

          have h0: "u\<in>(U \<inter> U') \<Longrightarrow> {u} \<subseteq> (U \<union> U')" for u by blast

          from E1_is have "?lhs = measure_pmf.prob (Pi_pmf V False (\<lambda>_. bernoulli_pmf p)) (\<Union>u\<in>U \<inter> U'. {S. S u \<and> card {u\<in>(U \<union> U'). S u} = 1 \<and> S \<sqsubseteq> V})" by presburger
          also from measure_pmf.finite_measure_finite_Union[OF p1 p2 p3] have "... = (\<Sum>u\<in>(U \<inter> U'). measure_pmf.prob (Pi_pmf V False (\<lambda>_. bernoulli_pmf p)) {S. S u \<and> card {u'\<in>(U \<union> U'). S u'} = 1 \<and> S \<sqsubseteq> V})" .
          also from Pi_set_E1 have "... = (\<Sum>u\<in>(U \<inter> U'). measure_pmf.prob (Pi_pmf V False (\<lambda>_. bernoulli_pmf p)) (PiE_dflt V False (\<lambda>v. (if v \<in> (U \<union> U') then {v = u} else UNIV))))" by simp
          also have "... = (\<Sum>u\<in>(U \<inter> U').  (\<Prod>v\<in>(U \<union> U'). pmf (bernoulli_pmf p) (v = u)))"  by (simp only: measure_Pi_pmf_PiE_dflt_subset[OF subset_U_U' assms(3)] measure_pmf_single)
          also have "... = (\<Sum>u\<in>(U \<inter> U').  (\<Prod>v\<in>(U \<union> U') - {u}. pmf (bernoulli_pmf p) (v = u)) * (\<Prod>v\<in>{u}. pmf (bernoulli_pmf p) (v = u)))" by (simp add: prod.subset_diff[of "{_}" "(U \<union> U')" "\<lambda>v. pmf (bernoulli_pmf p) (v = _)", OF h0 finite_UnI[OF finite_U finite_U']])  
          also have "... = (card (U \<inter> U') * p * (1 - p) ^ (card (U \<union> U') - 1))" using bernoulli_True bernoulli_False by fastforce
          finally show "?lhs = ?rhs" .
        qed

        have Pi_set_E2: "\<lbrakk>u \<in> U - U'; u' \<in> U' - U\<rbrakk> \<Longrightarrow> {S. S u \<and> S u' \<and> card {u\<in>(U \<union> U'). S u} = 2 \<and> S \<sqsubseteq> V} = (PiE_dflt V False (\<lambda>v. (if v \<in> (U \<union> U') then {v = u \<or> v = u'} else UNIV)))" (is "\<lbrakk>?asm1; ?asm2\<rbrakk> \<Longrightarrow> ?lhs = ?rhs") for u u'
        proof
          assume asm1: ?asm1 and asm2: ?asm2
          show "?lhs \<subseteq> ?rhs"
          proof
            fix S assume "S \<in> ?lhs" hence a0: "S u" and a1: "S u'" and a2: "card {u \<in> U \<union> U'. S u} = 2" and a3: "S \<sqsubseteq> V" by blast+
            from asm1 asm2 have a4: "u \<noteq> u'" by blast
            from a0 a1 asm1 asm2 have a5: "{u, u'} \<subseteq> {u \<in> U \<union> U'. S u}" by blast
            from card_subset_eq[OF _ a5] a2 a4 finite_UnI[OF finite_U finite_U'] have a6: "{u, u'} = {u \<in> U \<union> U'. S u}" by force
            from a6 have a7: "\<forall>v\<in>V. (v \<in> (U \<union> U')) \<longrightarrow> S v = (v = u \<or> v = u')" by blast
            from a3 have "\<forall>v\<in>UNIV - V. \<not>S v" by fastforce
            with a7 show "S \<in> ?rhs" unfolding PiE_dflt_def by force
          qed
        next
          assume asm1: ?asm1 and asm2: ?asm2
          show "?rhs \<subseteq> ?lhs"
          proof
            fix S assume "S \<in> ?rhs" hence a0: "\<forall>v\<in>V. (v \<in> (U \<union> U')) \<longrightarrow> S v = (v = u \<or> v = u')" and a1: "\<forall>v\<in>UNIV - V. \<not>S v" unfolding PiE_dflt_def by fastforce+
            from asm1 asm2 have a2: "u \<noteq> u'" by blast
            from asm1 asm2 a0 assms(4,5) have a3: "S u" and a4: "S u'" and a5: "{u \<in> U \<union> U'. S u} = {u, u'}" by blast+
            from a1 have a6: "S \<sqsubseteq> V" by auto
            from a2 a3 a4 a5 a6 show "S \<in> ?lhs" by force 
          qed
        qed

        have case_2: "measure_pmf.prob (Pi_pmf V False (\<lambda>_. bernoulli_pmf p)) ?E2 = card (U - U') * card (U' - U) * p ^ 2 * (1 - p) ^ (card (U \<union> U') - 2)" (is "?lhs = ?rhs")
        proof -

          have E2_is: "?E2 = (\<Union>u\<in>U - U'. \<Union>u'\<in>U'- U. {S. S u \<and> S u' \<and> card {u\<in>(U \<union> U'). S u} = 2 \<and> S \<sqsubseteq> V})" (is "?lhs1 = ?rhs1")
          proof
            show "?lhs1 \<subseteq> ?rhs1"
            proof
              fix S assume "S \<in> ?lhs1" hence a0: "card {u \<in> U - U'. S u} = 1" and a1: "card {u \<in> U' - U. S u} = 1" and a2: "card {u \<in> U \<union> U'. S u} = 2" and a3: "S \<sqsubseteq> V" by blast+
              from a0 have "\<exists>v. {u \<in> U - U'. S u} = {v}" by (meson card_1_singletonE) then obtain u where a4: "u \<in> U - U'" and S_u: "S u" by blast+
              from a1 have "\<exists>v. {u \<in> U' - U. S u} = {v}" by (meson card_1_singletonE) then obtain u' where a5: "u' \<in> U' - U" and S_u': "S u'" by blast+
              from a4 a5 S_u S_u' a2 a3 show "S \<in> ?rhs1" by blast
            qed
          next
            show "?rhs1 \<subseteq> ?lhs1"
            proof
              fix S assume "S \<in> ?rhs1" then obtain u u' where a0: "u \<in> U - U'" and a1: "u' \<in> U' - U" and a2: "S \<in> {S. S u \<and> S u' \<and> card {u \<in> U \<union> U'. S u} = 2 \<and> S \<sqsubseteq> V}" by blast
              from a2 have a3: "S u" and a4: "S u'" and a5: "card {u \<in> U \<union> U'. S u} = 2" and a6: "S \<sqsubseteq> V" by blast+
              from a0 a1 have a7: "u \<noteq> u'" by fast
              from a0 a1 a3 a4 have a8: "{u, u'} \<subseteq> {u \<in> U \<union> U'. S u}" by fast
              from card_subset_eq[OF _ a8] a5 a7 finite_UnI[OF finite_U finite_U'] have a9: "{u, u'} = {u \<in> U \<union> U'. S u}" by force
              from a0 a1 a9 have a10: "{u \<in> U - U'. S u} = {u}" by blast
              from a0 a1 a9 have a11: "{u \<in> U' - U. S u} = {u'}" by fast
              from a5 a6 a10 a11 show "S \<in> ?lhs1" by simp
            qed
          qed

          have p1: "finite (U - U')" using finite_U finite_U' by simp
          have p2: "(\<lambda>x. (\<Union>u'\<in>U'- U. {S. S x \<and> S u' \<and> card {u\<in>(U \<union> U'). S u} = 2 \<and> S \<sqsubseteq> V})) ` (U - U') \<subseteq> measure_pmf.events (Pi_pmf V False (\<lambda>_. bernoulli_pmf p))" by force
          have p3: "disjoint_family_on (\<lambda>x.  (\<Union>u'\<in>U' - U. {S. S x \<and> S u' \<and> card {u\<in>(U \<union> U'). S u} = 2 \<and> S \<sqsubseteq> V})) (U - U')" unfolding disjoint_family_on_def
          proof (standard, standard, standard, standard, standard)
            fix m n S
            assume a1: "m \<in> U - U'" and a2: "n \<in> U - U'" and a3: "m \<noteq> n" and a4: "S \<in> (\<Union>u'\<in>U'- U. {S. S m \<and> S u' \<and> card {u\<in>(U \<union> U'). S u} = 2 \<and> S \<sqsubseteq> V}) \<inter> (\<Union>u'\<in>U' - U. {S. S n \<and> S u' \<and> card {u\<in>(U \<union> U'). S u} = 2 \<and> S \<sqsubseteq> V})"
            from a4 have "\<exists>u'\<in>U' - U. S \<in> {S. S m \<and> S n \<and> S u' \<and> card {u\<in>(U \<union> U'). S u} = 2 \<and> S \<sqsubseteq> V}" by blast
            then obtain u' where a5: "u' \<in> U' - U" and a6: "S u'" by blast
            from a4 have a7: "S m" and a8: "S n" and a9: "card {u\<in>(U \<union> U'). S u} = 2" by blast+
            from a1 a5 have a10: "m \<noteq> u'" by blast
            from a2 a5 have a11: "n \<noteq> u'" by blast
            from a1 a2 a5 a6 a7 a8 have a12: "{n, m, u'} \<subseteq> {u\<in>(U \<union> U'). S u}" by fast
            from a3 a10 a11 have a13: "card {n, m, u'} = 3" by fastforce
            have "finite {u \<in> U \<union> U'. S u}" by (simp add: finite_U finite_U')
            from card_mono[OF this a12] a9 a13 show "S \<in> {}" by linarith
          qed (simp)

          have p4: "finite (U' - U)" using finite_U finite_U' by simp
          have p5: "y \<in> (U - U') \<Longrightarrow> (\<lambda>z. {S. S y \<and> S z \<and> card {u\<in>(U \<union> U'). S u} = 2 \<and> S \<sqsubseteq> V}) ` (U' - U) \<subseteq> measure_pmf.events (Pi_pmf V False (\<lambda>_. bernoulli_pmf p))" for y by force
          have p6: "y \<in> (U - U') \<Longrightarrow> disjoint_family_on (\<lambda>z. {S. S y \<and> S z \<and> card {u\<in>(U \<union> U'). S u} = 2 \<and> S \<sqsubseteq> V}) (U' - U)" for y unfolding disjoint_family_on_def
          proof (standard, standard, standard, standard, standard)
            fix m n S
            assume a1: "y \<in> (U - U')" and a2: "m \<in> U' - U" and a3: "n \<in> U' - U" and a4: "m \<noteq> n" and a5: "S \<in> {S. S y \<and> S m \<and> card {u\<in>(U \<union> U'). S u} = 2 \<and> S \<sqsubseteq> V} \<inter> {S. S y \<and> S n \<and> card {u\<in>(U \<union> U'). S u} = 2 \<and> S \<sqsubseteq> V}"
            from a5 have a6: "S y" and a7: "S m" and a8: "S n" and a9: "card {u\<in>(U \<union> U'). S u} = 2" by blast+
            from a1 a2 have a10: "m \<noteq> y" by blast
            from a1 a3 have a11: "n \<noteq> y" by blast
            from a1 a2 a3 a6 a7 a8 have a12: "{n, m, y} \<subseteq> {u\<in>(U \<union> U'). S u}" by fast
            from a4 a10 a11 have a13: "card {n, m, y} = 3" by fastforce
            have "finite {u \<in> U \<union> U'. S u}" by (simp add: finite_U finite_U')
            from card_mono[OF this a12] a9 a13 show "S \<in> {}" by linarith
          qed (simp)

          have h0: "\<lbrakk>u\<in>(U - U'); u'\<in>(U'-U)\<rbrakk> \<Longrightarrow> {u, u'} \<subseteq> (U \<union> U')" for u u' by blast
          have h1: "\<lbrakk>u\<in>(U - U'); u'\<in>(U'-U)\<rbrakk> \<Longrightarrow> (\<Prod>v\<in>(U \<union> U') - {u, u'}. pmf (bernoulli_pmf p) (v = u \<or> v = u')) * (\<Prod>v\<in>{u, u'}. pmf (bernoulli_pmf p) (v = u \<or> v = u')) = p ^ 2 * (1 - p) ^ (card (U \<union> U') - 2)" (is "\<lbrakk>?asm1; ?asm2\<rbrakk> \<Longrightarrow> ?lhs1 = ?rhs1") for u u'
          proof -
            assume asm1: ?asm1 and asm2: ?asm2
            hence u_noteq_u': "u \<noteq> u'" by blast
            from asm1 asm2 show "?lhs1 = ?rhs1" by (simp add: bernoulli_True bernoulli_False power2_eq_square[of p] u_noteq_u' eval_nat_numeral)
          qed

          from E2_is have "?lhs = measure_pmf.prob (Pi_pmf V False (\<lambda>_. bernoulli_pmf p)) (\<Union>u\<in>U - U'. \<Union>u'\<in>U'- U. {S. S u \<and> S u' \<and> card {u\<in>(U \<union> U'). S u} = 2 \<and> S \<sqsubseteq> V})" by presburger
          also from measure_pmf.finite_measure_finite_Union[OF p1 p2 p3] have "... = (\<Sum>u\<in>(U - U'). measure_pmf.prob (Pi_pmf V False (\<lambda>_. bernoulli_pmf p)) (\<Union>u'\<in>U'- U. {S. S u \<and> S u' \<and> card {u\<in>(U \<union> U'). S u} = 2 \<and> S \<sqsubseteq> V}))" .
          also from measure_pmf.finite_measure_finite_Union[OF p4 p5 p6] have "... = (\<Sum>u\<in>(U - U'). \<Sum>u'\<in>(U'- U). measure_pmf.prob (Pi_pmf V False (\<lambda>_. bernoulli_pmf p)) {S. S u \<and> S u' \<and> card {u\<in>(U \<union> U'). S u} = 2 \<and> S \<sqsubseteq> V})" by fastforce
          also from Pi_set_E2 have "... = (\<Sum>u\<in>(U - U'). \<Sum>u'\<in>(U' - U). measure_pmf.prob (Pi_pmf V False (\<lambda>_. bernoulli_pmf p)) (PiE_dflt V False (\<lambda>v. (if v \<in> (U \<union> U') then {v = u \<or> v = u'} else UNIV))))" by simp
          also have "... = (\<Sum>u\<in>(U - U'). \<Sum>u'\<in>(U' - U).  (\<Prod>v\<in>(U \<union> U'). pmf (bernoulli_pmf p) (v = u \<or> v = u')))"  by (simp only: measure_Pi_pmf_PiE_dflt_subset[OF subset_U_U' assms(3)] measure_pmf_single)
          also have "... = (\<Sum>u\<in>(U - U'). \<Sum>u'\<in>(U' - U).  (\<Prod>v\<in>(U \<union> U') - {u, u'}. pmf (bernoulli_pmf p) (v = u \<or> v = u')) * (\<Prod>v\<in>{u, u'}. pmf (bernoulli_pmf p) (v = u \<or> v = u')))" by (simp add: prod.subset_diff[of "{_,_}" "(U \<union> U')" "\<lambda>v. pmf (bernoulli_pmf p) (v = _ \<or> v = _)", OF h0 finite_UnI[OF finite_U finite_U']])
          also have "... = (\<Sum>u\<in>(U - U'). \<Sum>u'\<in>(U' - U).  p ^ 2 * (1 - p) ^ (card (U \<union> U') - 2))" using h1 by simp
          also have "... = card (U - U') * card (U' - U) * p ^ 2 * (1 - p) ^ (card (U \<union> U') - 2)" by force
          finally show "?lhs = ?rhs" .
        qed
  
        from a_is_1 have "measure_pmf.prob (random_subset V p) {S. Some (intersect U S) = x i \<and> Some (intersect U' S) = x i \<and> S \<sqsubseteq> V}
                   = measure_pmf.prob (Pi_pmf V False (\<lambda>_. bernoulli_pmf p)) {S. card {u\<in>U. S u} = 1 \<and> card {u\<in>U'. S u} = 1 \<and> S \<sqsubseteq> V}" using Some by simp
        also have "... = measure_pmf.prob (Pi_pmf V False (\<lambda>_. bernoulli_pmf p)) ?E1 + measure_pmf.prob (Pi_pmf V False (\<lambda>_. bernoulli_pmf p)) ?E2" using measure_pmf.finite_measure_Union[OF _ _ dsjnt_cases] two_cases by fastforce
        also have "... = card (U \<inter> U') * p * (1 - p) ^ (card (U \<union> U') - 1) + card (U - U') * card (U' - U) * p ^ 2 * (1 - p) ^ (card (U \<union> U') - 2)" by (simp only: case_1 case_2)
        also have "... = r * p * (1 - p) ^ (2 * d - r - 1) + (d - r) * (d - r) * p ^ 2 * (1 - p) ^ (2 * d - r - 2)" using card_U_Int_U' card_diffU card_diffU' card_U_Un_U' by presburger
        also have "... = (1 - p) ^ (2 * d - r) * (p * r / (1 - p)) + (d - r) * (d - r) * p ^ 2 * (1 - p) ^ (2 * d - r - 2)" using power_diff[of "1 - p", OF _ exponent_is_nat1] p_less_1 by force
        also have "... = (1 - p) ^ (2 * d - r) * (p * r / (1 - p)) + (1 - p) ^ (2 * d - r) * ((d - r) ^ 2 * p ^ 2 / (1 - p) ^ 2)" using power_diff[of "1 - p", OF _ exponent_is_nat2] p_less_1 power2_eq_square[of "d - r"] by force
        also have "... = (1 - p) ^ (2 * d - r) * (p * r / (1 - p)) + (1 - p) ^ (2 * d - r) * (((d - r) * p / (1 - p)) ^ 2)" by (simp add: power_divide power_mult_distrib)
        also have "... = (1 - p) ^ (2 * d - r) * ((p * r)/(1 - p) + ((p * (d - r))/(1 - p))^2)" by (simp add: distrib_left mult.commute)
        finally show ?thesis by (simp add: a_is_1 Some)
      qed
    qed
  qed

  have "measure_pmf.prob (vector_of (random_subset V p) n) {Ss. map_vector (intersect U) Ss = x \<and> map_vector (intersect U') Ss = x \<and> (\<forall>S\<in>range Ss. S \<sqsubseteq> V)} = measure_pmf.prob (vector_of (random_subset V p) n) (PiE_dflt {i. i<n} None (\<lambda>i. {S. map_option (intersect U) S = x i \<and> map_option (intersect U') S = x i \<and> (case S of Some s \<Rightarrow> s \<sqsubseteq> V | None \<Rightarrow> True)}))" by (simp only: Pi_set_vector)
  also have "... = (\<Prod>i\<in>{i. i<n}. measure_pmf.prob (random_subset V p) {S. Some (intersect U S) = x i \<and> Some (intersect U' S) = x i \<and> S \<sqsubseteq> V})" by (simp add: measure_Pi_pmf_PiE_dflt)
  also have "... = (\<Prod>i\<in>{i. i<n}. (1 - p) ^ (2 * d - r) * ((p * r)/(1-p) + ((p * (d-r))/(1-p))^2)^(the (x i)))" using inner by fastforce
  also have "... = (\<Prod>i\<in>{i. i<n}. (1 - p) ^ (2 * d - r)) * ((\<Prod>i\<in>{i. i<n}. ((p * r)/(1-p) + ((p * (d-r))/(1-p))^2)^(the (x i))))" by (simp only: prod.distrib)
  also have "... = ((1 - p) ^ (2 * d - r))^n * ((\<Prod>i\<in>{i. i<n}. ((p * r)/(1-p) + ((p * (d-r))/(1-p))^2)^(the (x i))))" by (simp only: prod_constant card_Collect_less_nat)
  also have "... = ((1 - p) ^ ((2 * d - r) * n)) * ((p * r)/(1-p) + ((p * (d-r))/(1-p))^2)^(count x 1)" by (simp only: zero_one_vector_prod[OF vect_x fin_x len_x rng_x] semiring_normalization_rules) 
  finally show ?thesis .
qed





end
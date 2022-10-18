
theory Lemma
  imports Main "HOL-Probability.Probability_Mass_Function" "HOL-Probability.Product_PMF" Vector
begin
  
fun rnd_sbst :: "'a set \<Rightarrow> real \<Rightarrow> ('a \<Rightarrow> bool) pmf" where
  "rnd_sbst V p = Pi_pmf V False (\<lambda>_. bernoulli_pmf p)"

fun vector_of :: "'a pmf \<Rightarrow> nat \<Rightarrow> 'a vector pmf" where
  "vector_of f n = Pi_pmf {i::nat. i < n} None (\<lambda>i. if i < n then map_pmf Some f else return_pmf None)"

fun intersect :: "'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> nat" where
  "intersect U S = card {u\<in>U. S u}"

fun intersect2 :: "'a set \<Rightarrow> ('a \<Rightarrow> bool) vector \<Rightarrow> nat vector" where
  "intersect2 U = map_vector (intersect U)"

lemma 
  assumes "0 \<le> p" and "p \<le> 1" and "Finite_Set.finite V" and "U \<subseteq> V" and "U' \<subseteq> V" and 
          "card U = d" and "card U' = d" and "card (U \<inter> U') = r" and 
          fin_x: "finite x" and vect_x: "vector x" and rng_x: "range x = {0, 1}" and len_x: "length x = n"
  shows "measure_pmf.prob (vector_of (rnd_sbst V p) n) {Ss. intersect2 U Ss = x \<and> intersect2 U' Ss = x} = ((1 - p) ^ ((2 * d - r) * n)) * ((p * r)/(1-p) + ((p * (d-r))/(1-p))^2)^(count x 1)"
proof -

  note finite_U = finite_subset[OF assms(4) assms(3)]
  note finite_U' = finite_subset[OF assms(5) assms(3)]

  have Pi_set_rewrite_1: "{Ss. intersect2 U Ss = x \<and> intersect2 U' Ss = x} = (PiE_dflt {i. i<n} None (\<lambda>i. {S. map_option (intersect U) S = x i \<and> map_option (intersect U') S = x i}))" (is "?lhs = ?rhs")
  proof
    show "?lhs \<subseteq> ?rhs"
    proof 
      fix Ss assume asm: "Ss \<in> ?lhs" hence 0: "intersect2 U Ss = x" and 1: "intersect2 U' Ss = x" by blast+
      from 0 have 00: "\<forall>i<n. map_option (intersect U) (Ss i) = x i" by fastforce
      from 1 have 11: "\<forall>i<n. map_option (intersect U') (Ss i) = x i" by fastforce
      from map_vector_vector vect_x 0 have "vector Ss" by auto
      moreover from map_vector_fin fin_x 0 have "finite Ss" by auto 
      moreover from map_vector_len len_x 0 have "length Ss = n" by auto
      ultimately have "\<forall>i\<ge>n. Ss i = None" using len_ge_None by blast
      with 00 11 show "Ss \<in> ?rhs" unfolding PiE_dflt_def by simp
    qed
  next
    show "?rhs \<subseteq> ?lhs"
    proof
      fix Ss assume "Ss \<in> ?rhs" 
      hence 0: "\<forall>i<n. map_option (intersect U) (Ss i) = x i" and 1: "\<forall>i<n. map_option (intersect U') (Ss i) = x i" and 2: "\<forall>i\<ge>n. Ss i = None" unfolding PiE_dflt_def by auto
      from map_vector_inverse[OF vect_x fin_x len_x 0 2] map_vector_inverse[OF vect_x fin_x len_x 1 2] show "Ss \<in> ?lhs" by simp
    qed
  qed
  
  have Pi_set_rewrite_2: "{S. card {u\<in>U. S u} = 0 \<and> card {u\<in>U'. S u} = 0} = (\<Pi> v\<in>V. {v \<notin> (U \<union> U'), False})" (is "?lhs = ?rhs")
  proof
    show "?lhs \<subseteq> ?rhs" sorry
  next
    show "?rhs \<subseteq> ?lhs" sorry
  qed

  have inner: "i < n \<Longrightarrow> measure_pmf.prob (rnd_sbst V p) {S. Some (intersect U S) = x i \<and> Some (intersect U' S) = x i} 
        = (1 - p) ^ (2 * d - r) * ((p * r)/(1-p) + ((p * (d-r))/(1-p))^2)^(the (x i))" for i
  proof (cases "x i")
    case None
    assume "i < n" hence "i < length x" using len_x by blast
    from len_less_Some[OF vect_x fin_x this] None have "False" by blast
    then show ?thesis ..
  next
    case (Some a)
    assume "i < n"
    have dsjnt: "(U \<union> U') \<inter> (V - (U \<union> U')) = {}" by simp
    have union: "U \<union> U' \<union> (V - (U \<union> U')) = V" using assms(4,5) by blast
    have bernoulli_prob_space: "space (measure_pmf (bernoulli_pmf p)) = {True, False}" by force
    have card_U_U': "card (U \<union> U') = 2 * d - r" by (metis assms(6,7,8) add_diff_cancel_right' card_Un_Int finite_U finite_U' mult_2)
    have card_diffU: "card (U - U') = d - r" by (simp add: assms(6) assms(8) card_Diff_subset_Int finite_U')
    have card_diffU': "card (U' - U) = d - r" by (simp add: assms(7) assms(8) card_Diff_subset_Int finite_U' inf_commute)
    show ?thesis
    proof (cases a)
      case 0
      from 0 have "measure_pmf.prob (rnd_sbst V p) {S. Some (intersect U S) = x i \<and> Some (intersect U' S) = x i}
      =  measure_pmf.prob (rnd_sbst V p) {S. card {u\<in>U. S u} = 0 \<and> card {u\<in>U'. S u} = 0}" using Some by force
      also have "... = measure_pmf.prob (Pi_pmf V False (\<lambda>_. bernoulli_pmf p)) {S. card {u\<in>U. S u} = 0 \<and> card {u\<in>U'. S u} = 0}" using Some by simp
      also have "... = measure_pmf.prob (Pi_pmf V False (\<lambda>_. bernoulli_pmf p)) (\<Pi> v\<in>V. {v \<notin> (U \<union> U'), False})" by (simp only: Pi_set_rewrite_2)
      also have "... = (\<Prod>v\<in>V. measure_pmf.prob (bernoulli_pmf p) {v \<notin> (U \<union> U'), False})" using measure_Pi_pmf_Pi[OF assms(3)] by fast
      also have "... = (\<Prod>v\<in>(U \<union> U'). measure_pmf.prob (bernoulli_pmf p) {v \<notin> (U \<union> U'), False}) * (\<Prod>v\<in>V - (U \<union> U'). measure_pmf.prob (bernoulli_pmf p) {v \<notin> (U \<union> U'), False})" 
        using prod.union_disjoint[OF finite_UnI[OF finite_U finite_U'] finite_Diff[OF assms(3), of "U \<union> U'"] dsjnt] union by metis
      also have "... = (\<Prod>v\<in>(U \<union> U'). measure_pmf.prob (bernoulli_pmf p) {False}) * (\<Prod>v\<in>V - (U \<union> U'). measure_pmf.prob (bernoulli_pmf p) {True, False})" by fastforce
      also have "... = (\<Prod>v\<in>(U \<union> U'). measure_pmf.prob (bernoulli_pmf p) {False}) * (\<Prod>v\<in>V - (U \<union> U'). 1)" using measure_pmf.prob_space[of "bernoulli_pmf p"] bernoulli_prob_space by force
      also have "... = (\<Prod>v\<in>(U \<union> U'). pmf (bernoulli_pmf p) False) * (\<Prod>v\<in>V - (U \<union> U'). 1)" by (simp only: measure_pmf_single[of "bernoulli_pmf p" False])
      also have "... = (\<Prod>v\<in>(U \<union> U'). pmf (bernoulli_pmf p) False)" using prod.neutral_const by force
      also have "... = (1 - p) ^ (2 * d - r)" using assms(1) assms(2) card_U_U' by force
      finally show ?thesis by (simp add: 0 Some)
    next
      case (Suc nat) hence "a \<noteq> 0" by fast
      with vector_range_Some[of x, OF Some] rng_x have a_is_1: "a = 1" by simp

      let ?E1 = "{S. card {u\<in>(U \<inter> U'). S u} = 1 \<and> card {u\<in>(U \<union> U'). S u} = 1}"
      let ?E2 = "{S. card {u\<in>(U - U'). S u} = 1 \<and> card {u\<in>(U' - U). S u} = 1 \<and> card {u\<in>(U \<union> U'). S u} = 2}"
      have two_cases: "{S. card {u\<in>U. S u} = 1 \<and> card {u\<in>U'. S u} = 1} = ?E1 \<union> ?E2" sorry
      have dsjnt_cases: "?E1 \<inter> ?E2 = {}" by auto

      have case_1: "measure_pmf.prob (Pi_pmf V False (\<lambda>_. bernoulli_pmf p)) ?E1 = card (U \<inter> U') * p * (1 - p) ^ (card (U \<union> U') - 1)" (is "?lhs = ?rhs")
      proof -
        have "?E1 = (\<Union>u\<in>U \<inter> U'. {S. S u \<and> card {u\<in>(U \<union> U'). S u} = 1})" (is "?lhs1 = ?rhs1")
        proof
          show "?lhs1 \<subseteq> ?rhs1"
          proof
            fix S assume "S \<in> ?lhs1" hence a: "card {u\<in>(U \<inter> U'). S u} = 1" and b: "card {u\<in>(U \<union> U'). S u} = 1" by blast+
            from a have "\<exists>u \<in> U \<inter> U'. S u" by (metis (no_types, lifting) a_is_1 Collect_empty_eq \<open>a \<noteq> 0\<close> card.empty)
            with b show "S \<in> ?rhs1" by blast
          qed
        next
          show "?rhs1 \<subseteq> ?lhs1"
          proof
            fix S assume "S \<in> ?rhs1" then obtain u where a: "u \<in> U \<inter> U'" and b: "S u" and c: "card {u\<in>(U \<union> U'). S u} = 1" by blast+
            hence subset_1: "{u \<in> U \<inter> U'. S u} \<subseteq> {u \<in> U \<union> U'. S u}" by blast
            from card_mono[OF _ this] c have card_less_than_1: "card {u \<in> U \<inter> U'. S u} \<le> 1" by fastforce

            from finite_subset[OF subset_1] c have set_is_finite: "Finite_Set.finite {u \<in> U \<inter> U'. S u}" by fastforce
            
            from a b have subset_2: "{u} \<subseteq> {u \<in> U \<inter> U'. S u}" by blast
            from card_mono[OF set_is_finite this] card_less_than_1 have "card {u \<in> U \<inter> U'. S u} = 1" by simp
            with c show "S \<in> ?lhs1" by blast
          qed
        qed
        have "Finite_Set.finite ?E1" using measure_measure_pmf_finite sorry
        show "?lhs = ?rhs" sorry
      qed

      have case_2: "measure_pmf.prob (Pi_pmf V False (\<lambda>_. bernoulli_pmf p)) ?E2 = card (U - U') * card (U' - U) * p ^ 2 * (1 - p) ^ (card (U \<union> U') - 2)" (is "?lhs = ?rhs")
      proof -
        show "?lhs = ?rhs" sorry
      qed

      from a_is_1 have "measure_pmf.prob (rnd_sbst V p) {S. Some (intersect U S) = x i \<and> Some (intersect U' S) = x i}
      =  measure_pmf.prob (rnd_sbst V p) {S. card {u\<in>U. S u} = 1 \<and> card {u\<in>U'. S u} = 1}" using Some by force
      also have "... = measure_pmf.prob (Pi_pmf V False (\<lambda>_. bernoulli_pmf p)) {S. card {u\<in>U. S u} = 1 \<and> card {u\<in>U'. S u} = 1}" using Some by simp
      also have "... = measure_pmf.prob (Pi_pmf V False (\<lambda>_. bernoulli_pmf p)) ?E1 + measure_pmf.prob (Pi_pmf V False (\<lambda>_. bernoulli_pmf p)) ?E2" using measure_pmf.finite_measure_Union[OF _ _ dsjnt_cases] two_cases by force
      also have "... = card (U \<inter> U') * p * (1 - p) ^ (card (U \<union> U') - 1) + card (U - U') * card (U' - U) * p ^ 2 * (1 - p) ^ (card (U \<union> U') - 2)" by (simp only: case_1 case_2)
      also have "... = r * p * (1 - p) ^ (2 * d - r - 1) + (d - r) * (d - r) * p ^ 2 * (1 - p) ^ (2 * d - r - 2)" using assms(8) card_diffU card_diffU' card_U_U' by presburger
      also have "... = ((r * p * (1 - p) ^ (2 * d - r - 1)) * (1 - p) / (1 - p)) + (d - r) * (d - r) * p ^ 2 * (1 - p) ^ (2 * d - r - 2)" sorry
      finally show ?thesis sorry
    qed
  qed

  have "measure_pmf.prob (vector_of (rnd_sbst V p) n) {Ss. intersect2 U Ss = x \<and> intersect2 U' Ss = x} = measure_pmf.prob (vector_of (rnd_sbst V p) n) (PiE_dflt {i. i<n} None (\<lambda>i. {S. map_option (intersect U) S = x i \<and> map_option (intersect U') S = x i}))" by (simp only: Pi_set_rewrite_1)
  also have "... = (\<Prod>i\<in>{i. i<n}. measure_pmf.prob (rnd_sbst V p) {S. Some (intersect U S) = x i \<and> Some (intersect U' S) = x i})" by (simp add: measure_Pi_pmf_PiE_dflt)
  also have "... = (\<Prod>i\<in>{i. i<n}. (1 - p) ^ (2 * d - r) * ((p * r)/(1-p) + ((p * (d-r))/(1-p))^2)^(the (x i)))" using inner by fastforce
  also have "... = (\<Prod>i\<in>{i. i<n}. (1 - p) ^ (2 * d - r)) * ((\<Prod>i\<in>{i. i<n}. ((p * r)/(1-p) + ((p * (d-r))/(1-p))^2)^(the (x i))))" by (simp only: prod.distrib)
  also have "... = ((1 - p) ^ (2 * d - r))^n * ((\<Prod>i\<in>{i. i<n}. ((p * r)/(1-p) + ((p * (d-r))/(1-p))^2)^(the (x i))))" by (simp only: prod_constant card_Collect_less_nat)
  also have "... = ((1 - p) ^ ((2 * d - r) * n)) * ((p * r)/(1-p) + ((p * (d-r))/(1-p))^2)^(count x 1)" by (simp only: zero_one_vector_prod[OF vect_x fin_x len_x rng_x] semiring_normalization_rules) 
  finally show ?thesis .
qed




end
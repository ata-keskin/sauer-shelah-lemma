theory Corollary_6_4
  imports Main 6_3
begin

corollary corollary_6_4: 
  assumes "0 \<le> p" and "p < 1" and "finite V" and "U \<subseteq> V" and 
          "card U = d" and "finite (dom x)" and "vector x" and "ran x \<subseteq> {0, 1}" and "len x = n"
  shows "measure_pmf.prob (pmf_vector (random_subset V p) n) {T. ran T \<subseteq> power_set V \<and> map_vector ((\<lambda>_ S. card {u\<in>U. S u})) T = x} = (1 - p) ^ (d * n) * ((p * d)/(1-p))^(count x 1)"
  using lemma_6_3[OF assms(1,2,3,4,4,5,5) _ assms(6,7,8,9), of d] assms(5) by fastforce

corollary independent_events:
  assumes "0 \<le> p" and "p < 1" and "finite V" and "U \<subseteq> V" and "U' \<subseteq> V" and "card U = card U'"
          "U \<inter> U' = {}" and "finite (dom x)" and "vector x" and "ran x \<subseteq> {0, 1}" and "len x = n"
  shows "prob_space.indep_events (measure_pmf (pmf_vector (random_subset V p) n)) (\<lambda>U. {T. map_vector (\<lambda>_ S. card {u\<in>U. S u}) T = x \<and> ran T \<subseteq> power_set V}) {U, U'}"
proof (rule prob_space.indep_eventsI[OF measure_pmf.prob_space_axioms], simp)
  have intersection: "{T. ran T \<subseteq> power_set V \<and> map_vector (\<lambda>_ S. card {u \<in> U. S u}) T = x} \<inter> {T. ran T \<subseteq> power_set V \<and> map_vector (\<lambda>_ S. card {u \<in> U'. S u}) T = x}
      = {T. ran T \<subseteq> power_set V \<and> map_vector (\<lambda>_ S. card {u \<in> U. S u}) T = x \<and> map_vector (\<lambda>_ S. card {u \<in> U'. S u}) T = x}" by fast
  have "measure_pmf.prob (pmf_vector (random_subset V p) n) 
      ({T. ran T \<subseteq> power_set V \<and> map_vector (\<lambda>_ S. card {u \<in> U. S u}) T = x} \<inter> {T. ran T \<subseteq> power_set V \<and> map_vector (\<lambda>_ S. card {u \<in> U'. S u}) T = x}) =
      measure_pmf.prob (pmf_vector (random_subset V p) n) ({T. ran T \<subseteq> power_set V \<and> map_vector (\<lambda>_ S. card {u \<in> U. S u}) T = x \<and> map_vector (\<lambda>_ S. card {u \<in> U'. S u}) T = x})" by (simp only: intersection)
  also have "... = (measure_pmf.prob (pmf_vector (random_subset V p) n) {T. ran T \<subseteq> power_set V \<and> map_vector (\<lambda>_ S. card {u \<in> U. S u}) T = x}) * (measure_pmf.prob (pmf_vector (random_subset V p) n) 
      {T. ran T \<subseteq> power_set V \<and> map_vector (\<lambda>_ S. card {u \<in> U'. S u}) T = x})"
    by (simp only: lemma_6_3[OF assms(1,2,3,4,5,6) _ _ assms(8,9,10,11)] assms(6,7) 
          corollary_6_4[OF assms(1,2,3,4) _ assms(8,9,10,11), of "card U"]
          corollary_6_4[OF assms(1,2,3,5) _ assms(8,9,10,11), of "card U'"], 
        simp add: mult.assoc power2_eq_square power_divide power_even_eq power_mult_distrib)
  
  
end
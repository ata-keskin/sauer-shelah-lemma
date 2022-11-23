theory Corollary_6_4
  imports Main Lemma_6_3
begin

corollary corollary_6_4: 
  assumes "0 \<le> p" and "p < 1" 
      and "finite V" and "U \<subseteq> V" and "card U = d"
      and "x \<in> \<llangle>{0,1}\<rrangle>^n"
  shows "measure_pmf.prob (pmf_vector (random_subset V p) n) {T \<in> \<llangle>power_set V\<rrangle>^n. map_vector ((\<lambda>_ S. card {u\<in>U. S u})) T = x} = \<Phi> p d x d"
  using lemma_6_3[OF assms(1,2,3,4,4,5,5) _ assms(6), of d] assms(5) by fastforce

corollary independent_events:
  assumes "0 \<le> p" and "p < 1" 
      and "finite V" and "U \<subseteq> V" and "U' \<subseteq> V" and "card U = card U'" and "U \<inter> U' = {}"
      and "x \<in> \<llangle>{0,1}\<rrangle>^n"
  shows "prob_space.indep_events (measure_pmf (pmf_vector (random_subset V p) n)) (\<lambda>U. {T \<in> \<llangle>power_set V\<rrangle>^n. map_vector (\<lambda>_ S. card {u\<in>U. S u}) T = x}) {U, U'}"
proof (rule prob_space.indep_eventsI[OF measure_pmf.prob_space_axioms], simp)
  fix J assume asm0: "J \<subseteq> {U, U'}" and asm1: "finite J" and asm2: "J \<noteq> {}"
  let ?goal = "measure_pmf.prob (pmf_vector (random_subset V p) n) (\<Inter>i\<in>J. {T \<in> \<llangle>power_set V\<rrangle>^n. map_vector (\<lambda>_ S. card {u \<in> i. S u}) T = x}) 
               = (\<Prod>i\<in>J. measure_pmf.prob (pmf_vector (random_subset V p) n) {T \<in> \<llangle>power_set V\<rrangle>^n. map_vector (\<lambda>_ S. card {u \<in> i. S u}) T = x})"
  have intersection: "{T \<in> \<llangle>power_set V\<rrangle>^n. map_vector (\<lambda>_ S. card {u \<in> U. S u}) T = x} \<inter> {T \<in> \<llangle>power_set V\<rrangle>^n. map_vector (\<lambda>_ S. card {u \<in> U'. S u}) T = x}
      = {T \<in> \<llangle>power_set V\<rrangle>^n. map_vector (\<lambda>_ S. card {u \<in> U. S u}) T = x \<and> map_vector (\<lambda>_ S. card {u \<in> U'. S u}) T = x}" by fast
  have "measure_pmf.prob (pmf_vector (random_subset V p) n) 
      ({T \<in> \<llangle>power_set V\<rrangle>^n. map_vector (\<lambda>_ S. card {u \<in> U. S u}) T = x} \<inter> {T \<in> \<llangle>power_set V\<rrangle>^n. map_vector (\<lambda>_ S. card {u \<in> U'. S u}) T = x}) =
      measure_pmf.prob (pmf_vector (random_subset V p) n) ({T \<in> \<llangle>power_set V\<rrangle>^n.  map_vector (\<lambda>_ S. card {u \<in> U. S u}) T = x \<and> map_vector (\<lambda>_ S. card {u \<in> U'. S u}) T = x})" by (simp only: intersection)
  also have "... = (measure_pmf.prob (pmf_vector (random_subset V p) n) {T \<in> \<llangle>power_set V\<rrangle>^n. map_vector (\<lambda>_ S. card {u \<in> U. S u}) T = x}) * (measure_pmf.prob (pmf_vector (random_subset V p) n) 
      {T \<in> \<llangle>power_set V\<rrangle>^n.  map_vector (\<lambda>_ S. card {u \<in> U'. S u}) T = x})"
    by (simp only: lemma_6_3[OF assms(1,2,3,4,5,6) _ _ assms(8)] assms(6,7) \<Phi>_def
          corollary_6_4[OF assms(1,2,3,4) _ assms(8), of "card U"]
          corollary_6_4[OF assms(1,2,3,5) _ assms(8), of "card U'"], 
        simp add: mult.assoc power2_eq_square power_divide power_even_eq power_mult_distrib)
  finally have independence: "measure_pmf.prob (pmf_vector (random_subset V p) n) 
      ({T \<in> \<llangle>power_set V\<rrangle>^n. map_vector (\<lambda>_ S. card {u \<in> U. S u}) T = x} \<inter> {T \<in> \<llangle>power_set V\<rrangle>^n. map_vector (\<lambda>_ S. card {u \<in> U'. S u}) T = x}) = (measure_pmf.prob (pmf_vector (random_subset V p) n) {T \<in> \<llangle>power_set V\<rrangle>^n. map_vector (\<lambda>_ S. card {u \<in> U. S u}) T = x}) * (measure_pmf.prob (pmf_vector (random_subset V p) n) 
      {T \<in> \<llangle>power_set V\<rrangle>^n.  map_vector (\<lambda>_ S. card {u \<in> U'. S u}) T = x})" .
  show ?goal
  proof (cases "J = {U, U'}")
    case J_is: True
    show ?thesis
    proof (cases "U = U'")
      case True
      with J_is show ?thesis by simp
    next
      case False
      from J_is have "measure_pmf.prob (pmf_vector (random_subset V p) n)
     (\<Inter>i\<in>J. {T \<in> \<llangle>power_set V\<rrangle>^n. map_vector (\<lambda>_ S. card {u \<in> i. S u}) T = x}) = measure_pmf.prob (pmf_vector (random_subset V p) n)
     ({T \<in> \<llangle>power_set V\<rrangle>^n. map_vector (\<lambda>_ S. card {u \<in> U. S u}) T = x} \<inter> {T \<in> \<llangle>power_set V\<rrangle>^n. map_vector (\<lambda>_ S. card {u \<in> U'. S u}) T = x})" by fastforce
    with J_is False show ?thesis by (simp only: independence, simp)
  qed
  next
    case False
    with asm0 asm1 asm2 obtain X where "J = {X}" by blast
    with False show ?thesis by force
  qed
qed
  
end
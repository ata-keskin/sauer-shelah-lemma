theory Corollary_6_4
  imports Main Lemma_6_3
begin

corollary corollary_6_4: 
  assumes "0 \<le> p" and "p < 1" and "finite V" and "U \<subseteq> V" and 
          "card U = d" and "Vector.finite x" and "vector x" and "range x \<subseteq> {0, 1}" and "length x = n"
  shows "measure_pmf.prob (vector_of (random_subset V p) n) {Ss. map_vector (intersect U) Ss = x \<and> (\<forall>S\<in>range Ss. S \<sqsubseteq> V)} = (1 - p) ^ (d * n) * ((p * d)/(1-p))^(count x 1)"
  using lemma_6_3[OF assms(1,2,3,4,4,5,5) _ assms(6,7,8,9), of d] assms(5) by fastforce

end
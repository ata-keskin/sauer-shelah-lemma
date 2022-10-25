theory Lemma_6_3_Extra
  imports Main Vector "HOL-Probability.Probability_Mass_Function" "HOL-Probability.Product_PMF"
begin

fun random_subset :: "'a set \<Rightarrow> real \<Rightarrow> ('a \<Rightarrow> bool) pmf" where
  "random_subset V p = Pi_pmf V False (\<lambda>_. bernoulli_pmf p)"

fun vector_of :: "'a pmf \<Rightarrow> nat \<Rightarrow> 'a vector pmf" where
  "vector_of f n = Pi_pmf {i::nat. i < n} None (\<lambda>i. if i < n then map_pmf Some f else return_pmf None)"

fun intersect :: "'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> nat" where
  "intersect U S = card {u\<in>U. S u}"

fun subsetof :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" (infixl "\<sqsubseteq>" 60) where
  "S \<sqsubseteq> V = (\<forall>u. S u \<longrightarrow> u \<in> V)"

lemma subsetof_Pow: "{S. S \<sqsubseteq> X} = (\<lambda>S x. x \<in> S) ` Pow X" by force
lemma finite_fPow: "finite X \<Longrightarrow> finite {S. S \<sqsubseteq> X}" by (metis subsetof_Pow finite_Pow_iff finite_imageI)

lemma measure_Pi_pmf_PiE_dflt_subset:
  assumes "U \<subseteq> V" and "finite V"
  shows "measure_pmf.prob (Pi_pmf V dflt p) (PiE_dflt V dflt (\<lambda>x. if x \<in> U then B x else UNIV)) = (\<Prod>x\<in>U. measure_pmf.prob (p x) (B x))" 
  by (simp add: measure_Pi_pmf_PiE_dflt[OF assms(2)] prod.subset_diff[OF assms])

end
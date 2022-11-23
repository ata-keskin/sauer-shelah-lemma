theory Pi_PMF_Lemmas
imports Main Vector "HOL-Probability.Product_PMF"
begin

definition pmf_vector :: "'a pmf \<Rightarrow> nat \<Rightarrow> 'a vector pmf" where
  "pmf_vector p n = Pi_pmf {i::nat. i < n} None (\<lambda>_. map_pmf Some p)"

definition power_set :: "'a set \<Rightarrow> ('a \<Rightarrow> bool) set" where 
 "power_set V = (\<lambda>S x. x \<in> S) ` (Pow V)"

fun random_subset :: "'a set \<Rightarrow> real \<Rightarrow> ('a \<Rightarrow> bool) pmf" where
  "random_subset V p = Pi_pmf V False (\<lambda>_. bernoulli_pmf p)"

lemma power_set_alt_def: "power_set V = {U. \<forall>x. U x \<longrightarrow> x \<in> V}"
  unfolding power_set_def by blast

lemma finite_power_set:
  assumes "finite V"
  shows "finite (power_set V)"
  unfolding power_set_def using finite_Pow_iff assms by blast

lemma set_pmf_random_subset:
  assumes "0 < p" and "p < 1" and "finite V"
  shows "set_pmf (random_subset V p) = power_set V"
proof-
  from set_Pi_pmf[OF assms(3), of False "(\<lambda>_. bernoulli_pmf p)"] set_pmf_bernoulli[OF assms(1,2)] 
  have "set_pmf (random_subset V p) = {f. \<forall>x. x\<notin>V \<longrightarrow> \<not>f x}" unfolding PiE_dflt_def comp_def by simp
  with power_set_alt_def[of V] show "set_pmf (random_subset V p) = power_set V" by force
qed

lemma set_pmf_pmf_vector:
  "set_pmf (pmf_vector p n) = \<llangle>set_pmf p\<rrangle>^n"
proof-
  from set_Pi_pmf[OF finite_Collect_less_nat[of n], of None "\<lambda>_. map_pmf Some p"] 
  have "set_pmf (pmf_vector p n) = {f. (\<forall>i. (i < n \<longrightarrow> f i \<in> Some ` set_pmf p) \<and> (i \<ge> n \<longrightarrow> f i = None))}" 
    unfolding pmf_vector_def PiE_dflt_def comp_def by fastforce
  with n_vectors_alt_def show ?thesis by auto
qed

lemma integrable_pmf_vector_finite:
  fixes f :: "'a vector \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "finite (set_pmf p)"
  shows "integrable (measure_pmf (pmf_vector p n)) f"
  by (simp add: set_pmf_pmf_vector[of p n] n_vectors_finite[OF assms, of n] integrable_measure_pmf_finite[of "pmf_vector p n" f])

lemma measure_Pi_pmf_PiE_dflt_subset:
  assumes "U \<subseteq> V" and "finite V"
  shows "measure_pmf.prob (Pi_pmf V dflt p) (PiE_dflt V dflt (\<lambda>x. if x \<in> U then B x else UNIV)) = (\<Prod>x\<in>U. measure_pmf.prob (p x) (B x))" 
  by (simp add: measure_Pi_pmf_PiE_dflt[OF assms(2)] prod.subset_diff[OF assms])

lemma measure_Pi_pmf_vector:
  assumes "x \<in> \<llangle>\<Omega>\<rrangle>^n"
  shows "measure_pmf.prob (pmf_vector p n) {T \<in> \<llangle>V\<rrangle>^n. (\<forall>f\<in>F. map_vector f T = x)} 
      = (\<Prod>i\<in>{i. i<n}. measure_pmf.prob p {T_i \<in> V. \<forall>f\<in>F. Some (f i T_i) = x i})"
proof -
  have "{T \<in> \<llangle>V\<rrangle>^n. (\<forall>f\<in>F. map_vector f T = x)} = (PiE_dflt {i. i<n} None (\<lambda>i. {T_i \<in> Some ` V. \<forall>f\<in>F. map_option (f i) T_i = x i}))" (is "?lhs = ?rhs")
  proof
    show "?lhs \<subseteq> ?rhs"
    proof 
      fix T assume asm: "T \<in> ?lhs" 
      then have map_T_i: "\<forall>f\<in>F. \<forall>i<n. map_option (f i) (T i) = x i" unfolding map_vector_def by fastforce
      with n_vectors_alt_def[of V n] asm show "T \<in> ?rhs" unfolding PiE_dflt_def by simp
    qed
  next
    show "?rhs \<subseteq> ?lhs"
    proof
      fix T assume "T \<in> ?rhs" 
      then have map_T_i: "\<forall>f\<in>F. \<forall>i<n. map_option (f i) (T i) = x i" and T_i_None: "\<forall>i\<ge>n. T i = None" and T_i_Some: "\<forall>i<n. (T i) \<in> Some ` V" unfolding PiE_dflt_def by auto
      with map_vector_iff[OF assms, of _ T] n_vectors_alt_def[of V n] show "T \<in> ?lhs" by force
    qed
  qed
  then have "measure_pmf.prob (pmf_vector p n) {T \<in> \<llangle>V\<rrangle>^n. (\<forall>f\<in>F. map_vector f T = x)} 
   = measure_pmf.prob (pmf_vector p n) (PiE_dflt {i. i<n} None (\<lambda>i. {T_i \<in> Some ` V. \<forall>f\<in>F. map_option (f i) T_i = x i}))" by presburger
  also have "...  = (\<Prod>i\<in>{i. i<n}. measure_pmf.prob p {T_i \<in> V. \<forall>f\<in>F. Some (f i T_i) = x i})" 
    unfolding pmf_vector_def using inj_image_mem_iff[OF injI, of "Some" _ V] by (simp add: measure_Pi_pmf_PiE_dflt[OF finite_Collect_less_nat, of n None])
  finally show ?thesis .
qed

lemma space_to_set_pmf: "measure_pmf.prob (p::'a pmf) {T \<in> space (measure_pmf p). P T} = measure_pmf.prob p {T \<in> set_pmf p. P T}"
    by (metis Collect_conj_eq Collect_mem_eq inf_commute inf_top_left measure_Int_set_pmf space_measure_pmf)

definition k_subset :: "'a set \<Rightarrow> nat \<Rightarrow> 'a set set" where
  "k_subset V k = {U \<in> Pow V. card U = k}"

lemma PiE_dflt_int: 
  "(PiE_dflt A dflt B1) \<inter> (PiE_dflt A dflt B2) = (PiE_dflt A dflt (\<lambda>x. (B1 x) \<inter> (B2 x)))" unfolding PiE_dflt_def by blast

lemma "U \<subseteq> V \<Longrightarrow> {S \<in> power_set V. card {u\<in>U. S u} = k} = (\<Union>S\<in>k_subset U k.(PiE_dflt V False (\<lambda>v. if v \<in> U then {v\<in>S} else UNIV)))" (is "?asm \<Longrightarrow> (?lhs = ?rhs)")
proof
  assume asm: ?asm
  show "?lhs \<subseteq> ?rhs"
  proof
    fix S assume "S \<in> ?lhs"
    hence S_subset_V: "S \<in> power_set V" and S_int_U: "card {u\<in>U. S u} = k" by blast+
    then have a0: "S \<in> (PiE_dflt V False (\<lambda>v. if v \<in> U then {v\<in>{u\<in>U. S u}} else UNIV))" unfolding PiE_dflt_def power_set_def by force
    from S_int_U have a1: "{u\<in>U. S u} \<in> k_subset U k" unfolding k_subset_def by blast
    from a0 a1 show "S \<in> ?rhs" by blast
  qed
next
  assume asm: ?asm
  show "?rhs \<subseteq> ?lhs"
  proof
    fix S assume "S \<in> ?rhs"
    then obtain S_k where a0: "S_k \<in> k_subset U k" and a1: "S \<in> (PiE_dflt V False (\<lambda>v. if v \<in> U then {v \<in> S_k} else UNIV))" by blast+
    hence a2: "S \<in> power_set V" unfolding PiE_dflt_def power_set_def by blast
    with a0 a1 asm have "S_k = {u\<in>U. S u}" unfolding PiE_dflt_def k_subset_def by fastforce
    with a0 have a3: "card {u\<in>U. S u} = k" unfolding k_subset_def by blast
    from a2 a3 show "S \<in> ?lhs" by blast
  qed
qed

end
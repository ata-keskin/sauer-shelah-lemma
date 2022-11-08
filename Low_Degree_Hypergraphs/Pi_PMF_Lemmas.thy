theory Pi_PMF_Lemmas
imports Main Vector "HOL-Probability.Product_PMF"
begin

definition pmf_vector :: "'a pmf \<Rightarrow> nat \<Rightarrow> 'a vector pmf" where
  "pmf_vector f n = Pi_pmf {i::nat. i < n} None (\<lambda>i. if i < n then map_pmf Some f else return_pmf None)"

definition power_set :: "'a set \<Rightarrow> ('a \<Rightarrow> bool) set" where 
 "power_set V = (\<lambda>S x. x \<in> S) ` (Pow V)"

fun random_subset :: "'a set \<Rightarrow> real \<Rightarrow> ('a \<Rightarrow> bool) pmf" where
  "random_subset V p = Pi_pmf V False (\<lambda>_. bernoulli_pmf p)"

lemma measure_Pi_pmf_PiE_dflt_subset:
  assumes "U \<subseteq> V" and "finite V"
  shows "measure_pmf.prob (Pi_pmf V dflt p) (PiE_dflt V dflt (\<lambda>x. if x \<in> U then B x else UNIV)) = (\<Prod>x\<in>U. measure_pmf.prob (p x) (B x))" 
  by (simp add: measure_Pi_pmf_PiE_dflt[OF assms(2)] prod.subset_diff[OF assms])

lemma measure_Pi_pmf_vector:
  assumes "vector x" and "finite (dom x)" and "F \<noteq> {}"
  shows "measure_pmf.prob (pmf_vector p (len x)) {T. ran T \<subseteq> X \<and> (\<forall>f\<in>F. map_vector f T = x)} 
      = (\<Prod>i\<in>{i. i<(len x)}. measure_pmf.prob p {T_i \<in> X. \<forall>f\<in>F. Some (f i T_i) = x i})"
proof -
  have "{T. ran T \<subseteq> X \<and> (\<forall>f\<in>F. map_vector f T = x)} = (PiE_dflt {i. i<(len x)} None (\<lambda>i. {T_i \<in> Some ` X. \<forall>f\<in>F. map_option (f i) T_i = x i}))" (is "?lhs = ?rhs")
  proof
    show "?lhs \<subseteq> ?rhs"
    proof 
      fix T assume asm: "T \<in> ?lhs" 
      then have map_T: "\<forall>f\<in>F. map_vector f T = x" and ran_subset_X: "ran T \<subseteq> X" by blast+
      from map_T have map_T_i: "\<forall>f\<in>F. \<forall>i<(len x). map_option (f i) (T i) = x i" unfolding map_vector_def by fastforce

      from map_vector_vector assms(1,3) map_T have vect_T: "vector T" by fast
      from map_vector_fin assms map_T have fin_T: "finite (dom T)" by fast
      from map_vector_len map_T assms(3) have len_T: "len T = len x" by fast
      from fin_vect_None_iff[OF vect_T fin_T] len_T have T_i_None: "\<forall>i\<ge>len x. T i = None" by simp
      from fin_vect_ran_subset_iff[OF vect_T fin_T] len_T ran_subset_X have T_i_Some: "\<forall>i<len x. (T i) \<in> Some ` X" by presburger
      from map_T_i T_i_None T_i_Some show "T \<in> ?rhs" unfolding PiE_dflt_def by force
    qed
  next
    show "?rhs \<subseteq> ?lhs"
    proof
      fix T assume "T \<in> ?rhs" 
      then have map_T_i: "\<forall>f\<in>F. \<forall>i<(len x). map_option (f i) (T i) = x i" and T_i_None: "\<forall>i\<ge>len x. T i = None" and T_i_Some: "\<forall>i<len x. (T i) \<in> Some ` X" unfolding PiE_dflt_def by auto
      from T_i_Some vectorI[OF T_i_None] None_notin_image_Some have vect_T: "vector T" by fast
      from finite_dom_iff_fin_vect T_i_None have fin_T: "finite (dom T)" by blast
      from T_i_Some fin_vect_ran_subset_iff[OF vect_T fin_T, of X] lenI[OF T_i_None] have "ran T \<subseteq> X" by fastforce
      with map_vector_iff[OF assms(1,2)] map_T_i T_i_None show "T \<in> ?lhs" by blast
    qed
  qed
  then have "measure_pmf.prob (pmf_vector p (len x)) {T. ran T \<subseteq> X \<and> (\<forall>f\<in>F. map_vector f T = x)} 
   = measure_pmf.prob (pmf_vector p (len x)) (PiE_dflt {i. i<len x} None (\<lambda>i. {T_i \<in> Some ` X. \<forall>f\<in>F. map_option (f i) T_i = x i}))" by presburger
  also have "...  = (\<Prod>i\<in>{i. i<(len x)}. measure_pmf.prob p {T_i \<in> X. \<forall>f\<in>F. Some (f i T_i) = x i})" 
    unfolding pmf_vector_def using inj_image_mem_iff[OF injI, of "Some" _ X] by (simp add: measure_Pi_pmf_PiE_dflt[OF finite_Collect_less_nat, of "len x" None])
  finally show ?thesis .
qed

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
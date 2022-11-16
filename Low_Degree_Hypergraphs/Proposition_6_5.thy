theory Proposition_6_5
  imports Main Lemma_6_3 Corollary_6_4 Other_Lemmas
begin

(* We can also replace these definitions by using https://www.isa-afp.org/theories/undirected_graph_theory/ *)
type_synonym 'a graph = "('a set) \<times> ('a set set)"
abbreviation vertices where "vertices \<equiv> fst"
abbreviation edges where "edges \<equiv> snd"
abbreviation well_formed where "well_formed G \<equiv> edges G \<subseteq> Pow (vertices G)"

definition regular :: "nat \<Rightarrow> 'a graph \<Rightarrow> bool" (infixl "regular" 80) where 
  "d regular G = (\<forall>e\<in>edges G. card e = d)"

proposition proposition_6_5: 
  assumes "0 \<le> p" and "p < 1" and finite_vertices: "finite V" and G_def: "G = (V, Z)" and wf: "well_formed G" and regular: "d regular G"
          and fin_vect_x: "x \<in> \<llangle>{0, 1}\<rrangle>^n"
        shows "measure_pmf.prob (pmf_vector (random_subset V p) n) {T \<in> \<llangle>power_set V\<rrangle>^n. x \<notin> {map_vector ((\<lambda>_ S. card {u\<in>U. S u})) T | U. U \<in> Z}} 
            \<le> measure_pmf.expectation (pmf_of_set (Z \<times> Z)) (\<lambda>(U, U'). exp ((((n * p) / (1-p)) + (n / p * (d^2))) * card (U \<inter> U'))) - 1"
proof (cases "p = 0 \<or> Z = {} \<or> d = 0")
  case True
  then show ?thesis sorry
next
  case _: False with assms(1) 
  have p_not_0: "p > 0" and Z_not_empty: "Z \<noteq> {}" and d_not_0: "d > 0" by (linarith, blast+)
  from finite_subset[OF assms(5)] finite_Pow_iff[of V] finite_vertices assms(4) have finite_edges: "finite Z" by simp
  from assms(4,5,6) have d_regular_G: "U \<in> Z \<Longrightarrow> card U = d" for U unfolding regular_def by simp

  let ?pmf_vect = "pmf_vector (random_subset V p) n" and ?Z_set = "\<lambda>T. {map_vector ((\<lambda>_ S. card {u\<in>U. S u})) T | U. U \<in> Z}"
  let ?M = "measure_pmf ?pmf_vect"
  note set_pmf_random_subset = set_pmf_random_subset[OF p_not_0 assms(2,3)]
  with set_pmf_pmf_vector[of "random_subset V p" n] have set_pmf_pmf_vector: "set_pmf ?pmf_vect = \<llangle>power_set V\<rrangle>^n" by argo


  let ?X = "\<lambda>U. (indicat_real {T. map_vector ((\<lambda>_ S. card {u\<in>U. S u})) T = x})"
  from integrable_pmf_vector_finite[of "(random_subset V p)" n "?X _"] set_pmf_random_subset finite_power_set[OF assms(3)] 
  have X_U_in_L1: "U \<in> Z \<Longrightarrow> integrable ?M (?X U)" for U by presburger

  let ?S = "\<lambda>T. \<Sum>U\<in>Z. ?X U T"
  have S_is_random_var: "measure_pmf.random_variable ?pmf_vect borel ?S" by force
  from integrable_pmf_vector_finite[of "(random_subset V p)" n "(\<lambda>x. (?S x)^2)"] set_pmf_random_subset finite_power_set[OF assms(3)]
  have S_in_L2: "integrable (measure_pmf ?pmf_vect) (\<lambda>x. (?S x)^2)" by argo
  from measure_pmf.square_integrable_imp_integrable[OF S_is_random_var S_in_L2] have S_in_L1: "integrable (measure_pmf ?pmf_vect) ?S" by blast

  have X_is_1_iff: "U \<in> Z \<Longrightarrow> ?X U T = 1 \<longleftrightarrow> map_vector ((\<lambda>_ S. card {u\<in>U. S u})) T = x" for U T unfolding indicator_def by force
  from corollary_6_4[OF assms(1,2,3) _ d_regular_G] assms(4,5)
  have corollary_6_4_for_U_in_Z: "U \<in> Z \<Longrightarrow> measure_pmf.prob ?pmf_vect {T \<in> \<llangle>power_set V\<rrangle>^n. map_vector ((\<lambda>_ S. card {u\<in>U. S u})) T = x} 
                  = (1 - p) ^ (d * n) * (p * real d / (1 - p)) ^ Vector.count x 1" for U by force

  let ?E_S = "measure_pmf.expectation ?pmf_vect ?S"
  \<comment>\<open>We now calculate the expected value of \<^term>\<open>?S\<close>.\<close>

  from Bochner_Integration.integral_sum[of Z ?M ?X] X_U_in_L1 have "?E_S = (\<Sum>U\<in>Z. measure_pmf.expectation ?pmf_vect (?X U))" by blast
  also from Bochner_Integration.integral_indicator[of ?M "{T. map_vector ((\<lambda>_ S. card {u\<in>_. S u})) T = x}"] 
  have "... = (\<Sum>U\<in>Z. measure_pmf.prob ?pmf_vect {T \<in> space ?M. map_vector ((\<lambda>_ S. card {u\<in>U. S u})) T = x})" by fastforce
  also from set_pmf_pmf_vector space_to_set_pmf[of ?pmf_vect] 
  have "... = (\<Sum>U\<in>Z. measure_pmf.prob ?pmf_vect {T \<in> \<llangle>power_set V\<rrangle>^n. map_vector ((\<lambda>_ S. card {u\<in>U. S u})) T = x})" by presburger
  also from corollary_6_4_for_U_in_Z have "... = (\<Sum>U\<in>Z. (1 - p) ^ (d * n) * (p * real d / (1 - p)) ^ Vector.count x 1)" by auto
  finally have E_S_val: "?E_S = card Z * ((1 - p) ^ (d * n) * (p * real d / (1 - p)) ^ Vector.count x 1)" by auto

  \<comment>\<open>We now calculate the expected value of \<^term>\<open>(\<lambda>T. (?S T)^2)\<close>.\<close>

  let ?X_mult = "\<lambda>U U' T. indicat_real {T. map_vector ((\<lambda>_ S. card {u\<in>U. S u})) T = x \<and> map_vector ((\<lambda>_ S. card {u\<in>U'. S u})) T = x} T"
  let ?X_mult' = "\<lambda>U U' T. map_vector ((\<lambda>_ S. card {u\<in>U. S u})) T = x \<and> map_vector ((\<lambda>_ S. card {u\<in>U'. S u})) T = x"

  have inter_1: "{T. map_vector ((\<lambda>_ S. card {u\<in>U::'a set. S u})) T = x} \<inter> {T. map_vector ((\<lambda>_ S. card {u\<in>U'. S u})) T = x} = {T. ?X_mult' U U' T}" for U U' by fastforce
  have indicator_mult: "?X U T * ?X U' T = ?X_mult (U::'a set) U' T" for U U' T
    by (subst indicator_inter_arith[symmetric], simp only: inter_1)

  have X_mult_summed_in_L1: "integrable ?M (\<lambda>T. \<Sum>U'\<in>Z. ?X_mult U U' T)" for U sorry
  have X_mult_in_L1: "integrable ?M (\<lambda>T. ?X_mult U U' T)" for U U' sorry

  from lemma_6_3[OF assms(1,2,3) _ _ d_regular_G d_regular_G refl vect_x fin_x ran_x len_x] assms(4,5) regular
  have lemma_6_3_for_U_in_Z: "\<lbrakk>U \<in> Z; U'\<in>Z\<rbrakk> \<Longrightarrow> measure_pmf.prob ?pmf_vect {T \<in> \<llangle>power_set V\<rrangle>^n. ?X_mult' U U' T} =
      (1 - p) ^ ((2 * d - card (U \<inter> U')) * n) * (p * card (U \<inter> U') / (1 - p) + (p * real (d - card (U \<inter> U')) / (1 - p))^2) ^ Vector.count x 1" for U U' sorry

  have "(?S T)^2 = (\<Sum>U\<in>Z. \<Sum>U'\<in>Z. ?X U T * ?X U' T)" for T
    by (subst sum_square_zero_one, auto simp add: finite_edges indicator_def)
  hence "measure_pmf.expectation ?pmf_vect (\<lambda>T. (?S T)^2) = measure_pmf.expectation ?pmf_vect (\<lambda>T. \<Sum>U\<in>Z. \<Sum>U'\<in>Z. ?X U T * ?X U' T)" by presburger
  also from indicator_mult
  have "... = measure_pmf.expectation ?pmf_vect (\<lambda>T. \<Sum>U\<in>Z. \<Sum>U'\<in>Z. ?X_mult U U' T)" by presburger
  also from Bochner_Integration.integral_sum[of Z ?M "(\<lambda>U T. \<Sum>U'\<in>Z. ?X_mult U U' T)"] X_mult_summed_in_L1
  have "... = (\<Sum>U\<in>Z. measure_pmf.expectation ?pmf_vect (\<lambda>T. \<Sum>U'\<in>Z. ?X_mult U U' T))" by blast
  also from Bochner_Integration.integral_sum[of Z ?M "(\<lambda>U' T. ?X_mult _ U' T)"] X_mult_in_L1
  have "... = (\<Sum>U\<in>Z. \<Sum>U'\<in>Z. measure_pmf.expectation ?pmf_vect (\<lambda>T. ?X_mult U U' T))" by presburger
  also from Bochner_Integration.integral_indicator[of ?M "{T. ?X_mult' _ _ T}"]
  have "... = (\<Sum>U\<in>Z. \<Sum>U'\<in>Z. measure_pmf.prob ?pmf_vect {T \<in> space ?M. ?X_mult' U U' T})" by auto
  also from set_pmf_pmf_vector space_to_set_pmf[of ?pmf_vect] 
  have "... = (\<Sum>U\<in>Z. \<Sum>U'\<in>Z. measure_pmf.prob ?pmf_vect {T \<in> \<llangle>power_set V\<rrangle>^n. ?X_mult' U U' T})" by presburger
  also from 



  \<comment>\<open>We now show the statement using the Chebyshev Inequality\<close>
  from Z_not_empty finite_edges have "card Z > 0" by fastforce
  with E_S_val assms(2) p_not_0 d_not_0 have E_S_positive: "0 < ?E_S" by fastforce

  have "measure_pmf.prob ?pmf_vect {T \<in> \<llangle>power_set V\<rrangle>^n. x \<notin> (?Z_set T)} 
      = measure_pmf.prob ?pmf_vect {T \<in> \<llangle>power_set V\<rrangle>^n. ?S T = 0}" sorry
  also from measure_pmf.finite_measure_mono have "... \<le> measure_pmf.prob ?pmf_vect {T \<in> \<llangle>power_set V\<rrangle>^n. ?E_S \<le> \<bar>?S T - ?E_S\<bar>}" sorry
  also from measure_pmf.Chebyshev_inequality[OF S_is_random_var S_in_L2 E_S_positive] 
  have "... \<le> (measure_pmf.variance ?pmf_vect ?S) / ?E_S^2" sorry
  also have "... = (measure_pmf.expectation ?pmf_vect (\<lambda>x. (?S x)^2)) / ?E_S^2 - 1" sorry
  
  

end
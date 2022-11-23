section "Vector"
theory Vector
  imports Main "HOL-Probability.Product_PMF"
begin

subsection "Definitions"

type_synonym 'a vector = "nat \<rightharpoonup> 'a"

definition vector :: "(nat \<rightharpoonup> 'a) \<Rightarrow> bool" where
  "vector v \<longleftrightarrow> (\<forall>n. v n \<noteq> None \<longrightarrow> (\<forall>i<n. v i \<noteq> None))"

definition len :: "'a vector \<Rightarrow> nat" where
  "len v = card (dom v)"

abbreviation nth :: "'a vector \<Rightarrow> nat \<Rightarrow> 'a" (infixl "!." 100) where
  "v !. n \<equiv> the (v n)"

definition cut :: "'a vector \<Rightarrow> nat \<Rightarrow> 'a vector" where
  "cut v n = (\<lambda>i::nat. if i \<ge> n then None else v i)"

definition map_vector :: "(nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a vector \<Rightarrow> 'b vector" where
  "map_vector f v = (\<lambda>i::nat. map_option (f i) (v i))"

definition n_vectors :: "'a set \<Rightarrow> nat \<Rightarrow> 'a vector set" ("/\<llangle>_/\<rrangle>^_" [0,999] 100) where
  "\<llangle>V\<rrangle>^n = {v::'a vector. vector v \<and> finite (dom v) \<and> len v = n \<and> ran v \<subseteq> V}"

definition prefix :: "'a vector \<Rightarrow> 'a vector \<Rightarrow> bool" (infixl "prefix" 100) where
  "u prefix v \<longleftrightarrow> (\<forall>i\<in>dom u. u i = v i)"

definition suffix :: "'a vector \<Rightarrow> 'a vector \<Rightarrow> bool" (infixl "suffix" 100) where
  "u suffix v \<longleftrightarrow> (\<exists>n. \<forall>i\<ge>n. u i = v (n + i))"

subsection "Basic Properties"

lemma vectorI: 
  assumes "\<forall>i\<ge>n. v i = None" and "\<forall>i<n. \<exists>x. v i = Some x"
  shows "vector v"
  by (metis Vector.vector_def assms dual_order.strict_trans1 linorder_le_cases option.distinct(1))

lemma vectorI2: 
  assumes "\<forall>i. \<exists>x. v i = Some x"
  shows "vector v"
  by (metis Vector.vector_def assms option.distinct(1))

lemma Some_vectorD: "\<lbrakk>vector v; v n \<noteq> None\<rbrakk> \<Longrightarrow> \<forall>i<n. v i \<noteq> None" unfolding vector_def by blast
lemma None_vectorD: "\<lbrakk>vector v; v n = None\<rbrakk> \<Longrightarrow> \<forall>i\<ge>n. v i = None" unfolding vector_def using order_le_imp_less_or_eq by blast
lemma less_vectorD: "\<lbrakk>vector v; v n \<noteq> None; v m = None\<rbrakk> \<Longrightarrow> n < m" by (meson leI None_vectorD)

\<comment> \<open>Finite vector introduction lemmas\<close>

lemma fin_iff: "finite (dom v) \<longleftrightarrow> (\<exists>n. \<forall>i\<ge>n. (v::'a vector) i = None)"
  by (metis (mono_tags, lifting) dom_def finite_nat_set_iff_bounded linorder_not_le mem_Collect_eq)

lemma fin_vect_vectorI: "v \<in> \<llangle>V\<rrangle>^n \<Longrightarrow> vector v" and
      fin_vect_finI:  "v \<in> \<llangle>V\<rrangle>^n \<Longrightarrow> finite (dom v)" and
      fin_vect_lenI:  "v \<in> \<llangle>V\<rrangle>^n \<Longrightarrow> len v = n" and
      fin_vect_ranI:  "v \<in> \<llangle>V\<rrangle>^n \<Longrightarrow> ran v \<subseteq> V" unfolding n_vectors_def by fast+

lemma domI: 
  assumes "vector v" and "finite (dom v)"
  shows "dom v = {i. i < (len v)}" 
proof-
  have "(\<exists>x. v (i::nat) = Some x) \<longleftrightarrow> i < (len v)" for i
  proof (standard, erule contrapos_pp)
    assume asm: "\<not> i < (len v)"
    have "i \<notin> dom v"
    proof (rule ccontr)
      assume "\<not>i \<notin> dom v" hence "i \<in> dom v" by blast
      with None_vectorD[OF assms(1)] have "{k. k \<le> i} \<subseteq> dom v" by fastforce
      from card_mono[OF assms(2) this] card_Collect_le_nat[of i] have "Suc i \<le> (len v)" unfolding len_def by fastforce
      with asm show "False" by simp
    qed
    hence "v i = None" unfolding dom_def by simp
    thus "\<not>(\<exists>x. v i = Some x)" by simp
  next
    assume asm: "(i::nat) < len v"
    have "i \<in> dom v"
    proof (rule ccontr)
      assume "i \<notin> dom v"
      from less_vectorD[OF assms(1)] this have "dom v \<subseteq> {k. k < i}" by blast
      from card_mono[OF _ this] card_Collect_le_nat[of i] asm show "False" unfolding len_def by simp
    qed
    hence "v i \<noteq> None" unfolding dom_def by simp
    hence "(\<exists>x\<in>ran v. v i = Some x)" unfolding ran_def by blast
    then show "\<exists>x. v i = Some x" by blast
  qed
  thus ?thesis unfolding dom_def by force
qed

lemma fin_vect_domI:
  assumes "v \<in> \<llangle>V\<rrangle>^n"
  shows "dom v = {i. i < n}"
  using domI assms unfolding n_vectors_def by blast

lemma infin_vect_domI:
  assumes "vector v" and "infinite (dom v)"
  shows "dom v = UNIV" 
  by (metis UNIV_eq_I assms(1) assms(2) domIff fin_iff None_vectorD)

lemma n_vectorsE: 
  assumes "v \<in> \<llangle>V\<rrangle>^n"
  shows "vector v" and "finite (dom v)" and "dom v = {i. i < n}" and "len v = n" and "ran v \<subseteq> V"
  using assms by (rule fin_vect_vectorI, rule fin_vect_finI, rule fin_vect_domI, rule fin_vect_lenI, rule fin_vect_ranI)

lemma n_vectorsI:
  assumes "\<forall>i<n.\<exists>x\<in>V. v i = Some x" and "\<forall>i\<ge>n. v i = None" 
  shows "v \<in> \<llangle>V\<rrangle>^n" 
proof-
  have 0: "vector v" by (meson vectorI assms)
  from fin_iff assms(2) have 1: "finite (dom v)" by blast
  from assms have "dom v = {i. i < n}" by (metis (mono_tags, lifting) Collect_cong dom_def linorder_le_less_linear option.discI)
  with card_Collect_less_nat have 2: "len v = n" unfolding len_def by simp
  have 3: "ran v \<subseteq> V"
  proof
    fix x assume "x \<in> ran v"
    then obtain i where "v i = Some x" unfolding ran_def by blast
    with assms show "x \<in> V" by (cases "i < n", auto)
  qed
  from 0 1 2 3 show ?thesis unfolding n_vectors_def by blast
qed

lemma n_vectors_alt_def: "\<llangle>V\<rrangle>^n = {v. (\<forall>i. (i < n \<longrightarrow> v i \<in> Some ` V) \<and> (i \<ge> n \<longrightarrow> v i = None))}" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof
    fix v assume asm: "v \<in> ?lhs"
    from fin_vect_domI[OF asm] fin_vect_ranI[OF asm] image_iff[of _ Some V] have 0: "\<forall>i. (i < n \<longrightarrow> v i \<in> Some ` V)" unfolding dom_def ran_def by blast
    from fin_vect_domI[OF asm] have 1: "\<forall>i. (i \<ge> n \<longrightarrow> v i = None)" unfolding dom_def using linorder_not_less by blast
    from 0 1 show "v \<in> ?rhs" by blast
  qed
next
  show "?rhs \<subseteq> ?lhs"
  proof
    fix v assume asm: "v \<in> ?rhs"
    from asm show "v \<in> ?lhs" by (subst n_vectorsI, blast+)
  qed
qed

lemma n_vectors_alt_def2: "\<llangle>V\<rrangle>^n = {v. dom v = {i. i < n} \<and> ran v \<subseteq> V}" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof
    fix v assume asm: "v \<in> ?lhs"
    from fin_vect_domI[OF asm] fin_vect_ranI[OF asm] show "v \<in> ?rhs" by blast
  qed
next
  show "?rhs \<subseteq> ?lhs"
  proof
    fix v assume asm: "v \<in> ?rhs"
    have "\<forall>i<n. \<exists>x\<in>V. v i = Some x" and "\<forall>i\<ge>n. v i = None" using asm unfolding ran_def dom_def by (blast, metis (mono_tags, lifting) asm domIff leD mem_Collect_eq)
    with n_vectorsI show "v \<in> ?lhs" by blast
  qed
qed

lemma n_vectors_obtain:
  assumes "v \<in> \<llangle>V\<rrangle>^n" and "0 < n"
  obtains x i where "i < n" and "x \<in> V" and "v i = Some x"
  using n_vectorsE[OF assms(1)] assms(2)
  by (metis domIff mem_Collect_eq option.exhaust ranI subset_eq)

lemma n_vectors_zero: "\<llangle>V\<rrangle>^0 = {Map.empty}" using n_vectors_alt_def[of V 0] by blast

lemma n_vectors_subset: 
  assumes "V \<subseteq> W"
  shows "\<llangle>V\<rrangle>^n \<subseteq> \<llangle>W\<rrangle>^n"
  using assms by (simp add: n_vectors_alt_def, blast)

lemma n_vectors_finite:
  assumes "finite V"
  shows "finite (\<llangle>V\<rrangle>^n)"
  using n_vectors_alt_def2[of V n] finite_set_of_finite_maps[OF finite_Collect_less_nat[of n] assms] by argo

lemma ran_alt_def:
  shows "ran v = the ` v ` dom v" unfolding ran_def dom_def by force

lemma nth_ranI:
  assumes "n \<in> dom v"
  shows "v !. n \<in> ran v"
  using assms unfolding dom_def ran_def by force

lemma nth_iff_Some:
  assumes "n \<in> dom v"
  shows "v !. n = x \<longleftrightarrow> v n = Some x"
  using assms unfolding dom_def by force

lemma prefix_alt_def:
  shows "u prefix v \<longleftrightarrow> v |` (dom u) = u"
proof
  assume "u prefix v"
  thus "v |` dom u = u" unfolding dom_def prefix_def restrict_map_def by fastforce
next
  assume "v |` (dom u) = u"
  hence "\<forall>i\<in>dom u. v |` (dom u) = u" by blast
  hence "(\<forall>i\<in>dom u. (if i \<in> dom u then v i else None) = u i)" using restrict_map_def[of v "dom u"] by metis
  hence "\<forall>i\<in>dom u. v i = u i" by presburger
  thus "u prefix v" unfolding prefix_def by presburger
qed

lemma empty_iff_fin_len_0: "v = Map.empty \<longleftrightarrow> finite (dom v) \<and> len v = 0" by (metis card_eq_0_iff dom_eq_empty_conv finite.emptyI len_def)

lemma empty_iff_ran_empty: "v = Map.empty \<longleftrightarrow> ran v = {}"
proof (standard, simp)
  assume "ran v = {}"
  then have "\<forall>i x. v i \<noteq> Some x" unfolding ran_def by simp
  hence "\<forall>i. v i = None" by simp
  thus "v = Map.empty" by blast
qed
  
subsection "Cut Lemmas"

lemma cut_vectorI: "vector v \<Longrightarrow> vector (cut v n)" unfolding vector_def by (metis Vector.cut_def dual_order.trans nat_less_le)

lemma cut_finI: "finite (dom (cut v n))" unfolding cut_def by (auto simp add: fin_iff)

lemma cut_domI: "dom (cut v n) = dom v \<inter> {i. i < n}" unfolding dom_def cut_def by force

lemma cut_lenI: 
  assumes "vector v" and "k \<le> len v"
  shows "len (cut v k) = k"
proof (cases "finite (dom v)")
  case True
  from domI[OF assms(1) True] assms(2) have "{i. i < k} \<subseteq> dom v" using leI subsetI by auto
  with cut_domI[of v k] card_Collect_less_nat[of k] show ?thesis unfolding len_def by (simp add: inf_absorb2)
next
  case False
  from infin_vect_domI[OF assms(1) False] cut_domI[of v k] card_Collect_less_nat[of k] show ?thesis unfolding len_def by simp
qed

lemma cut_ran_subset: "ran (cut v n) \<subseteq> ran v" unfolding ran_def cut_def by auto

lemma cut_empty: "cut v 0 = Map.empty" unfolding cut_def by simp

lemma fin_vect_cut:
  assumes "v \<in> \<llangle>V\<rrangle>^m"
  shows "(cut v n) \<in> (\<llangle>V\<rrangle>^(min m n))"
  using fin_vect_domI[OF assms] fin_vect_ranI[OF assms] cut_domI[of v n] cut_ran_subset[of v n]  
  by (subst n_vectors_alt_def2, force)
  
lemma len_cut_le: 
  shows "len (cut v n) \<le> n"
proof-
  from cut_domI[of v n] have "dom (cut v n) \<subseteq> {i. i < n}" by blast
  from card_mono[OF _ this] card_Collect_less_nat[of n] show ?thesis unfolding len_def by fastforce
qed 

subsection "Count Lemmas"

definition count :: "'a vector \<Rightarrow> 'a \<Rightarrow> nat" where
  "count v a = card (v -`{Some a})"

lemma count_alt_def: "count v x = card {i\<in>dom v. v i = Some x}" 
  unfolding dom_def count_def vimage_def by (simp, meson) 

lemma fin_vect_count:
  assumes "v\<in>\<llangle>V\<rrangle>^n"
  shows "count v x = count (cut v k) x + card {i. k \<le> i \<and> i < n \<and> v i = Some x}"
proof -
  have h0: "finite {i. i < n \<and> i < k \<and> v i = Some x}" by fast
  have h1: "finite {i. i < n \<and> i \<ge> k \<and> v i = Some x}" by fast
  have h2: "{i. i < n \<and> i < k \<and> v i = Some x} \<inter> {i. i < n \<and> i \<ge> k \<and> v i = Some x} = {}" by auto
  have h3: "{i. i < n \<and> v i = Some x} = {i. i < n \<and> i < k \<and> v i = Some x} \<union> {i. i < n \<and> i \<ge> k \<and> v i = Some x}" by fastforce
  have h4: "i < k \<Longrightarrow> v i = (cut v k) i" for i unfolding cut_def by auto

  have "count v x = card {i \<in> dom v. v i = Some x}" by (simp only: count_alt_def)
  also have "... = card {i. i < n \<and> v i = Some x}" by (simp add: fin_vect_domI[OF assms]) 
  also have "... = card {i. i < n \<and> i < k \<and> v i = Some x} + card {i. i < n \<and> i \<ge> k \<and> v i = Some x}" using card_Un_disjoint[OF h0 h1 h2] h3 by argo
  also have "... = card {i. i < n \<and> i < k \<and> (cut v k) i = Some x} + card {i. i < n \<and> i \<ge> k \<and> v i = Some x}" by (metis h4)
  also have "... = card {i \<in> dom (cut v k). (cut v k) i = Some x} + card {i \<in> dom v. i \<ge> k \<and> v i = Some x}" by (simp add: fin_vect_domI[OF assms] cut_domI)
  finally show ?thesis by (simp add: count_alt_def fin_vect_domI[OF assms], meson) 
qed

subsection "Map Vector Lemmas"

lemma map_vector_vector:
  shows "vector (map_vector f v) = vector v"
  unfolding map_vector_def vector_def by simp

lemma map_vector_fin:
  shows "finite (dom (map_vector f v)) = finite (dom v)"
  unfolding map_vector_def by (simp add: fin_iff)

lemma map_vector_dom:
  shows "dom (map_vector f v) = dom v"
  unfolding map_vector_def dom_def by force

lemma map_vector_len:
  shows "len (map_vector f v) = len v"
  unfolding len_def map_vector_def dom_def by force

lemma map_vector_ran:
  shows "ran (map_vector f v) \<subseteq> (\<Union>i\<in>dom v. image (f i) (ran v))"
proof
  fix x assume "x \<in> ran (map_vector f v)"
  then obtain i where m: "map_vector f v i = Some x" unfolding ran_def by blast
  with map_vector_dom[of f v] Map.domI have d: "i \<in> dom v" by blast
  then obtain z where "v i = Some z" and r: "z \<in> ran v" unfolding ran_def by blast+
  with m have "f i z = x" unfolding map_vector_def by simp
  with r have "x \<in> image (f i) (ran v)" by blast
  with d show "x \<in> (\<Union>i\<in>dom v. image (f i) (ran v))" by force
qed

lemma map_vector_iff:
  assumes "x \<in> \<llangle>V\<rrangle>^n"
  shows "((\<forall>i<n. map_option (f i) (v i) = x i) \<and> (\<forall>i\<ge>n. v i = None)) \<longleftrightarrow> map_vector f v = x" (is "?lhs1 \<and> ?lhs2 \<longleftrightarrow> ?rhs")
proof (auto, standard)
  assume lhs1: ?lhs1 and lhs2: ?lhs2
  fix i
  show "map_vector f v i = x i"
  proof (cases "i < n")
    case True
    with lhs1 show ?thesis unfolding map_vector_def n_vectors_def by simp
  next
    case False
    with lhs2 have 0: "map_vector f v i = None" unfolding map_vector_def by simp
    from fin_vect_domI[OF assms] False have "x i = None" by blast
    with 0 show ?thesis by simp
  qed
next
  fix i
  assume asm1: "x = map_vector f v" and asm2: "i < n"
  from assms asm1 asm2 show "map_option (f i) (v i) = map_vector f v i" unfolding map_vector_def by blast
next
  fix i
  assume asm1: "x = map_vector f v" and asm2: "n \<le> i"
  with fin_vect_domI[OF assms] map_vector_dom[of f v] show "v i = None" by (metis CollectD domIff leD)
qed

lemma fin_vect_map_vector:
  assumes "v \<in> \<llangle>U::'a set\<rrangle>^n"
  shows "map_vector f v \<in> \<llangle>\<Union>i \<in> {i. i < n}. image (f i) U\<rrangle>^n"
  using n_vectors_alt_def2[of "\<Union>i \<in> {i. i < n}. image (f i) U" n] 
        map_vector_ran[of f v] 
        map_vector_dom[of f v]
        fin_vect_ranI[OF assms]
        fin_vect_domI[OF assms]
  by force

subsection "Miscellaneous Lemmas"

lemma fin_vect_UNIV:
  assumes "x \<in> \<llangle>V\<rrangle>^n"
  shows "x \<in> \<llangle>UNIV\<rrangle>^n"
  using assms n_vectors_subset[of V UNIV n] by blast 

lemma fin_vect_induct[consumes 1, case_names Empty Cut FinVect]: 
  assumes "v \<in> \<llangle>V\<rrangle>^n"
  and "P Map.empty 0"
  and "(\<And>v n::nat. v \<in> \<llangle>V\<rrangle>^(Suc n) \<Longrightarrow> \<forall>k < Suc n. P (cut v k) k \<Longrightarrow> P v (Suc n))"
  shows "P v n"
using assms proof (induction n arbitrary: v rule: less_induct)
  case (less x)
  show ?case
  proof (cases x)
    case 0
    with less(2,3) n_vectors_zero show ?thesis by force
  next
    case (Suc nat)
    with less show ?thesis by (metis fin_vect_cut min.absorb4)
  qed
qed

lemma vector_equ: 
  assumes "v \<in> \<llangle>\<Omega>\<rrangle>^n" and "w \<in> \<llangle>\<Omega>\<rrangle>^n" and "\<forall>i<n. v i = w i"
  shows "v = w"
proof
  fix i
  show "v i = w i"
  proof (cases "i < n")
    case True
    then show ?thesis using assms by blast
  next
    case False
    from False fin_vect_domI[OF assms(1)] have 0: "v i = None" unfolding dom_def by blast
    from False fin_vect_domI[OF assms(2)] have 1: "w i = None" unfolding dom_def by blast
    from 0 1 show ?thesis by simp
  qed
qed

lemma zero_one_vector_sum:
  assumes "x\<in>\<llangle>{0,1}\<rrangle>^n"
  shows "(\<Sum>i::nat | i < n. N * x !. i) = N * (count x 1)"
using assms proof (induction x n rule: fin_vect_induct)
  case Empty
  then show ?case unfolding count_def by simp
next
  case (Cut v n)
  have nat_set: "{i. i \<le> n} - {n} = {i. i < n}" by force 
  have zero_one_vector_property: "card {i. n \<le> i \<and> i < Suc n \<and> v i = Some 1} = v !. n"
  proof (cases "v !. n")
    case 0
    then show ?thesis using less_Suc_eq_le by fastforce
  next
    case (Suc _) with fin_vect_domI[OF Cut(1)] fin_vect_ranI[OF Cut(1)] nth_ranI[of n v]
    have 1: "v !. n = 1" by auto
    with fin_vect_domI[OF Cut(1)] nth_iff_Some[of n v 1] 
    have "{i. n \<le> i \<and> i < Suc n \<and> v i = Some 1} = {n}" by force
    with 1 show ?thesis by force
  qed
  have "(\<Sum>i::nat | i < Suc n. N * v !. i) = (\<Sum>i | i \<le> n. N * v !. i)" using less_Suc_eq_le by presburger
  also from sum.subset_diff[OF _ finite_Collect_le_nat[of n], of "{n}" "\<lambda>i. N * v !. i"] nat_set 
  have "... = (\<Sum>i | i < n. N * v !. i) + N * v !. n" by fastforce
  also have "... = (\<Sum>i | i < n. N * (cut v n) !. i) + N * v !. n" unfolding cut_def by force
  also from Cut(2) have "... = N * (count (cut v n) 1 + v !. n)" by (simp add: distrib_left)
  finally show ?case using fin_vect_count[OF Cut(1), of 1 n] zero_one_vector_property by argo
qed

lemma zero_one_vector_prod:
  assumes "x\<in>\<llangle>{0,1}\<rrangle>^n"
  shows "(\<Prod>i | i < n. (N::'a::comm_semiring_1)^(x !. i)) = N^(count x 1)"
  using zero_one_vector_sum[OF assms, of 1] by (simp add: power_sum[symmetric])

end

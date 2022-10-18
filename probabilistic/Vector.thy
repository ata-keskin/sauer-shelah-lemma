theory Vector
  imports Main "HOL-Probability.Product_PMF"
begin

definition vector :: "(nat \<Rightarrow> 'a option) \<Rightarrow> bool" where
  "vector v \<equiv> (\<forall>n. v n \<noteq> None \<longrightarrow> (\<forall>i<n. v i \<noteq> None))"

type_synonym 'a vector = "nat \<Rightarrow> 'a option"

definition range :: "'a vector \<Rightarrow> 'a set" where
  "range v = {x. \<exists>n. v n = Some x}"

definition domain :: "'a vector \<Rightarrow> nat set" where
  "domain v = {n. v n \<noteq> None}"

definition finite :: "'a vector \<Rightarrow> bool" where
  "finite v \<longleftrightarrow> (\<exists>n. \<forall>i\<ge>n. v i = None)"

abbreviation infinite where "infinite v \<equiv> \<not> finite v"

definition length :: "'a vector \<Rightarrow> nat" where
  "length v = card (domain v)"

definition count :: "'a vector \<Rightarrow> 'a \<Rightarrow> nat" where
  "count v a = card (v -`{Some a})" 

definition map_vector :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a vector \<Rightarrow> 'b vector" where
  "map_vector f v = (\<lambda>i. map_option f (v i))"

definition cut :: "'a vector \<Rightarrow> nat \<Rightarrow> 'a vector" (infixl "|x" 60) where
  "v |x n = (\<lambda>i. if i \<ge> n then None else v i)"

lemma vector_Some: "\<lbrakk>vector v; v n \<noteq> None\<rbrakk> \<Longrightarrow> \<forall>i<n. v i \<noteq> None" unfolding vector_def by blast
lemma vector_None: "\<lbrakk>vector v; v n = None\<rbrakk> \<Longrightarrow> \<forall>i\<ge>n. v i = None" unfolding vector_def using order_le_imp_less_or_eq by blast

lemma vector_less: "\<lbrakk>vector v; v n \<noteq> None; v m = None\<rbrakk> \<Longrightarrow> n < m" by (meson leI vector_None)

lemma cut_vector: "vector v \<Longrightarrow> vector (v |x n)" unfolding vector_def by (metis Vector.cut_def dual_order.trans nat_less_le)

lemma cut_Some_less: "\<lbrakk>vector v; (v |x n) i \<noteq> None\<rbrakk> \<Longrightarrow> i < n" by (meson Vector.cut_def leI) 
lemma cut_Some: "(v |x n) i \<noteq> None \<Longrightarrow> (v |x n) i = v i" by (auto simp add: cut_def)

lemma finite_iff_domain_finite:
  shows "finite v \<longleftrightarrow> Finite_Set.finite (domain v)"
by (metis (mono_tags, lifting) Vector.finite_def domain_def finite_nat_set_iff_bounded linorder_not_le mem_Collect_eq)

lemma domain_empty_iff_len_0: "domain v = {} \<longleftrightarrow> finite v \<and> length v = 0" 
  by (metis card_0_eq finite.emptyI finite_iff_domain_finite length_def)

lemma not_in_domain_consecutive: 
  assumes "vector v" and "n \<notin> domain v"
  shows "\<forall>i \<ge> n. i \<notin> domain v"
  using assms vector_None domain_def by blast

lemma in_domain_consecutive: 
  assumes "vector v" and "n \<in> domain v"
  shows "\<forall>i \<le> n. i \<in> domain v"
  using assms vector_None domain_def by blast

lemma len_ge_None:
  assumes "vector v" and "finite v" and "i \<ge> length v"
  shows "v i = None"
proof-
  have finiteness: "Finite_Set.finite (domain v)" using finite_iff_domain_finite assms(2) by fast
  have "i \<notin> domain v"
  proof (rule ccontr)
    assume "\<not>i \<notin> domain v" hence "i \<in> domain v" by blast
    from in_domain_consecutive[OF assms(1) this] have "{k. k \<le> i} \<subseteq> domain v" by blast
    from card_mono[OF finiteness this] card_Collect_le_nat[of i] have "Suc i \<le> length v" unfolding length_def by simp
    with assms(3) show "False" by linarith
  qed
  thus "v i = None" unfolding domain_def by simp
qed

lemma len_less_Some:
  assumes "vector v" and "finite v" and "i < length v"
  shows "v i \<noteq> None"
proof-
  have finiteness: "Finite_Set.finite (domain v)" using finite_iff_domain_finite assms(2) by fast
  have "i \<in> domain v"
  proof (rule ccontr)
    assume "i \<notin> domain v"
    from not_in_domain_consecutive[OF assms(1) this] have "domain v \<subseteq> {k. k < i}" using linorder_not_le by blast
    from card_mono[OF _ this] card_Collect_le_nat[of i] assms(3) show "False" unfolding length_def by simp
  qed
  thus "v i \<noteq> None" unfolding domain_def by simp
qed

lemma finite_domain: 
  assumes "vector v" and "finite v"
  shows "domain v = {i. i < length v}" 
  by (metis (mono_tags, lifting) Collect_cong domain_def leI len_ge_None[OF assms(1)] len_less_Some[OF assms(1)] assms(2))

lemma infinite_domain:
  assumes "vector v" and "infinite v"
  shows "domain v = UNIV" 
  by (metis UNIV_eq_I finite_iff_domain_finite finite_nat_set_iff_bounded_le in_domain_consecutive[OF assms(1)] nle_le assms(2))

lemma infinite_len_0: "infinite v \<Longrightarrow> length v = 0"
  by (metis card_eq_0_iff finite_iff_domain_finite length_def)

lemma domain_cut: "domain (v |x n) = domain v \<inter> {i. i < n}" unfolding domain_def cut_def by force

lemma domain_cut_finite: 
  assumes "vector v" and "finite v"
  shows "domain (v |x n) = {i. i < min (length v) n}"
proof -
  from finite_domain[OF assms] have "domain v = {i. i < length v}" by (simp add: domain_def)
  then show "domain (v |x n) = {i. i < min (length v) n}" using domain_cut by auto
qed
lemma finite_cut: "finite (v |x n)" unfolding finite_def cut_def by fastforce

lemma length_cut_finite_le: 
  assumes "vector v" and "finite v"
  shows "length (v |x n) \<le> length v"
proof-
  have "domain (v |x n) \<subseteq> domain v"oops

lemma length_cut_le: 
  shows "length (v |x n) \<le> n"
proof-
  from domain_cut[of v n] have "domain (v |x n) \<subseteq> {i. i < n}" by blast
  from card_mono[OF _ this] card_Collect_less_nat[of n] show ?thesis unfolding length_def by fastforce
qed
  

lemma length_cut_equ: 
  assumes "vector v" and "length v \<ge> n"
  shows "length (v |x n) = n"
proof (cases "finite v")
  case True
  from domain_cut_finite[OF assms(1) True] have "length (v |x n) = card {i. i < min (length v) n}" unfolding length_def by fastforce
  also from assms(2) have "... = card {i. i < n}" by force
  also from card_Collect_less_nat have "... = n" by blast
  finally show ?thesis .
next
  case False
  from assms(2) infinite_len_0[OF False] have "n = 0" by linarith
  then show ?thesis unfolding domain_def length_def cut_def by simp
qed

lemma domain_cut_None: "\<lbrakk>vector v; v n = None\<rbrakk> \<Longrightarrow> domain v = domain (v |x n)" unfolding vector_def by (metis cut_def order_le_imp_less_or_eq) 

lemma domain_cut_Some: 
  assumes "vector v" and "finite v" and "v n \<noteq> None" and "length v \<ge> n"
  shows "domain v = domain (v |x n) \<union> {i. n \<le> i \<and> i < length v}" (is "?lhs = ?rhs")
proof -
  from finite_domain[OF assms(1) assms(2)] have "domain v = {i. i < length v}" by argo
  also from assms(4) have "... = {i. i < n} \<union> {i. n \<le> i \<and> i < length v}" by fastforce
  also from finite_domain[OF cut_vector[OF assms(1)] finite_cut, of n] length_cut_equ[OF assms(1) assms(4)] have "... = domain (v |x n) \<union> {i. n \<le> i \<and> i < length v}" by presburger
  finally show ?thesis .
qed

lemma vector_equal: 
  assumes "vector v" and "finite v" and "length v = n" and "vector w" and "finite w" and "length w = n" and "\<forall>i<n. v i = w i"
  shows "v = w"
proof
  fix i
  show "v i = w i"
  proof (cases "i < n")
    case True
    then show ?thesis using assms(7) by blast
  next
    case False
    from False len_ge_None[OF assms(1,2), of i] assms(3) have 0: "v i = None" by linarith
    from False len_ge_None[OF assms(4,5), of i] assms(6) have 1: "w i = None" by linarith
    from 0 1 show ?thesis by simp
  qed
qed

lemma vector_range_Some:
  assumes "v i = Some x"
  shows "x \<in> range v"
  using assms range_def by fastforce

lemma map_vector_vector:
  shows "vector v \<longleftrightarrow> vector (map_vector f v)"
  unfolding map_vector_def vector_def by simp

lemma map_vector_fin:
  shows "finite v \<longleftrightarrow> finite (map_vector f v)"
  unfolding finite_def map_vector_def by simp

lemma map_vector_len:
  shows "length v = length (map_vector f v)"
  unfolding length_def map_vector_def domain_def by force

lemma map_vector_eval[simp]:
  shows "map_vector f v i = map_option f (v i)"
  by (simp add: map_vector_def)

lemma map_vector_inverse:
  assumes "vector x" and "finite x" and "length x = n" and "\<forall>i<n. map_option f (v i) = x i" and "\<forall>i\<ge>n. v i = None"
  shows "map_vector f v = x"
proof
  fix i
  show "map_vector f v i = x i"
  proof (cases "i < n")
    case True
    with assms(4) show ?thesis by simp
  next
    case False
    with assms(5) have 0: "map_vector f v i = None" by simp
    from len_ge_None[OF assms(1,2), of i] assms(3) False have "x i = None" by simp
    with 0 show ?thesis by simp
  qed
qed

lemma zero_one_vector_prod:
  assumes "vector x" and "finite x" and "length x = n" and "range x = {0, 1}"
  shows "(\<Prod>i\<in>{i. i<(n::nat)}. N^(the (x i))) = N^(count x 1)"
proof (induction n arbitrary: x)
  case 0
  then show ?case sorry
next
  case (Suc n)
  show ?case sorry
qed

lemma zero_one_vector_sum:
  assumes "vector x" and "finite x" and "length x = n" and "range x = {0, 1}"
  shows "(\<Sum>i\<in>{i. i<(n::nat)}. N * (the (x i))) = N * (count x 1)"
proof (induction n arbitrary: x)
  case 0
  then show ?case sorry
next
  case (Suc n)
  show ?case sorry
qed

end

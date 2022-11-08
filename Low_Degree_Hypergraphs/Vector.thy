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

definition cut :: "'a vector \<Rightarrow> nat \<Rightarrow> 'a vector" (infixl "|x" 60) where
  "v |x n = (\<lambda>i. if i \<ge> n then None else v i)"

definition map_vector :: "(nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a vector \<Rightarrow> 'b vector" where
  "map_vector f v = (\<lambda>i. map_option (f i) (v i))"

subsection "Basic Properties"

lemma vectorI: 
  assumes "\<forall>i\<ge>n. v i = None" and "\<forall>i<n. v i \<noteq> None"
  shows "vector v"
  by (meson Vector.vector_def assms linorder_not_le order_less_trans)

lemma Some_vectorD: "\<lbrakk>vector v; v n \<noteq> None\<rbrakk> \<Longrightarrow> \<forall>i<n. v i \<noteq> None" unfolding vector_def by blast
lemma None_vectorD: "\<lbrakk>vector v; v n = None\<rbrakk> \<Longrightarrow> \<forall>i\<ge>n. v i = None" unfolding vector_def using order_le_imp_less_or_eq by blast
lemma less_vectorD: "\<lbrakk>vector v; v n \<noteq> None; v m = None\<rbrakk> \<Longrightarrow> n < m" by (meson leI None_vectorD)

\<comment> \<open>Lemmas about the domain\<close>

lemma finite_dom_iff_fin_vect: "finite (dom v) \<longleftrightarrow> (\<exists>n. \<forall>i\<ge>n. (v::'a vector) i = None)"
  by (metis (mono_tags, lifting) dom_def finite_nat_set_iff_bounded linorder_not_le mem_Collect_eq)

lemma fin_vect_Some_iff:
  assumes "vector v" and "finite (dom v)"
  shows "(\<exists>x\<in>ran v. v i = Some x) \<longleftrightarrow> i < len v"
proof (standard, erule contrapos_pp)
  assume asm: "\<not> i < len v"
  have "i \<notin> dom v"
  proof (rule ccontr)
    assume "\<not>i \<notin> dom v" hence "i \<in> dom v" by blast
    from this None_vectorD[OF assms(1)] have "{k. k \<le> i} \<subseteq> dom v" by fastforce
    from card_mono[OF assms(2) this] card_Collect_le_nat[of i] have "Suc i \<le> len v" unfolding len_def by simp
    with asm show "False" by linarith
  qed
  hence "v i = None" unfolding dom_def by simp
  thus "\<not>(\<exists>x\<in>ran v. v i = Some x)" by simp
next
  assume asm: "i < len v"
  have "i \<in> dom v"
  proof (rule ccontr)
    assume "i \<notin> dom v"
    from less_vectorD[OF assms(1)] this have "dom v \<subseteq> {k. k < i}" by blast
    from card_mono[OF _ this] card_Collect_le_nat[of i] asm show "False" unfolding len_def by simp
  qed
  hence "v i \<noteq> None" unfolding dom_def by simp
  thus "(\<exists>x\<in>ran v. v i = Some x)" unfolding ran_def by blast
qed

lemma fin_vect_None_iff:
  assumes "vector v" and "finite (dom v)"
  shows "v i = None \<longleftrightarrow> i \<ge> len v"
  using fin_vect_Some_iff[OF assms] by (metis not_Some_eq linorder_not_le ranI)

lemma infin_vect_dom:
  assumes "vector v" and "infinite (dom v)"
  shows "dom v = UNIV" 
  by (metis UNIV_eq_I assms(1) assms(2) domIff finite_dom_iff_fin_vect None_vectorD)

lemma infinite_len_0: "infinite (dom v) \<Longrightarrow> len v = 0"
  by (metis card_eq_0_iff len_def)

lemma fin_vect_dom: 
  assumes "vector v" and "finite (dom v)"
  shows "dom v = {i. i < len v}" 
  unfolding dom_def by (meson linorder_not_le fin_vect_None_iff[OF assms])

\<comment> \<open>Lemmas about the range\<close>
lemma fin_vect_ranE:
  assumes "vector v" and "finite (dom v)" and "x \<in> ran v"
  obtains i where "i < len v" and "v i = Some x"
proof-
  from assms(3) obtain i where a0: "v i = Some x" unfolding ran_def by blast
  from fin_vect_Some_iff[OF assms(1,2)] a0 assms(3) have a1: "i < len v" by blast
  from a0 a1 that show ?thesis by blast
qed

lemma fin_vect_ran_subset_iff: 
  assumes "vector v" and "finite (dom v)"
  shows "ran v \<subseteq> X \<longleftrightarrow> (\<forall>i<len v. v i \<in> Some ` X)"
  proof (standard, auto)
    fix i assume asm1: "ran v \<subseteq> X" and asm2: "i < len v"
    from fin_vect_Some_iff[OF assms] asm2 have "\<exists>x\<in>ran v. v i = Some x" by blast
    with asm1 show "v i \<in> Some ` X" by fast
  next
    fix x assume asm1: "\<forall>i<len v. v i \<in> Some ` X" and asm2: "x \<in> ran v"
    from fin_vect_ranE[OF assms asm2] obtain i where "i < len v" and "v i = Some x" by blast
    with asm1 show "x \<in> X" by fastforce
  qed

lemma len_le:
  assumes "\<forall>i\<ge>n. v i = None"
  shows "len v \<le> n"
proof-
  from assms have "dom v \<subseteq> {i. i < n}" unfolding dom_def by (metis (mono_tags, lifting) Collect_mono_iff leI)
  from card_mono[OF _ this] show ?thesis unfolding len_def by simp
qed

lemma len_ge:
  assumes "\<forall>i<n. v i \<noteq> None" and "finite (dom v)"
  shows "len v \<ge> n"
proof-
  from assms(1) have "{i. i < n} \<subseteq> dom v" unfolding dom_def by blast
  from card_mono[OF assms(2) this] show ?thesis unfolding len_def by simp
qed

lemma lenI:
  assumes "\<forall>i\<ge>n. v i = None" and "\<forall>i<n. v i \<noteq> None"
  shows "len v = n"
proof-
  from finite_dom_iff_fin_vect assms(1) have "finite (dom v)" by blast
  from len_le[OF assms(1)] len_ge[OF assms(2) this] show ?thesis by fastforce
qed

subsection "Cut Lemmas"

lemma cut_vectorI: "vector v \<Longrightarrow> vector (v |x n)" unfolding vector_def by (metis Vector.cut_def dual_order.trans nat_less_le)

lemma finite_dom_cut: "finite (dom (v |x n))" unfolding cut_def by (auto simp add: finite_dom_iff_fin_vect)

lemma cut_dom: "dom (v |x n) = dom v \<inter> {i. i < n}" unfolding dom_def cut_def by force

lemma fin_vect_cut_dom:
  assumes "vector v" and "finite (dom v)"
  shows "dom (v |x n) = {i. i < min (len v) n}"
  unfolding min_def using fin_vect_dom[OF assms] cut_dom[of v n] by force

lemma cut_ran_subset: "ran (v |x n) \<subseteq> ran v" unfolding ran_def cut_def by auto

lemma cut_len_le: 
  shows "len (v |x n) \<le> n"
proof-
  from cut_dom[of v n] have "dom (v |x n) \<subseteq> {i. i < n}" by blast
  from card_mono[OF _ this] card_Collect_less_nat[of n] show ?thesis unfolding len_def by fastforce
qed

lemma cut_len: 
  assumes "vector v" and "len v \<ge> n"
  shows "len (v |x n) = n"
proof (cases "finite (dom v)")
  case True
  from cut_dom fin_vect_cut_dom[OF assms(1) True] have "len (v |x n) = card {i. i < min (len v) n}" unfolding len_def by presburger
  also from assms(2) have "... = card {i. i < n}" by force
  also from card_Collect_less_nat have "... = n" by blast
  finally show ?thesis .
next
  case False
  from assms(2) infinite_len_0[OF False] have "n = 0" by linarith
  then show ?thesis unfolding dom_def len_def cut_def by simp
qed

lemma fin_vect_dom_cutI: 
  assumes "vector v" and "finite (dom v)"
  shows "dom v = dom (v |x n) \<union> {i. n \<le> i \<and> i < len v}" (is "?lhs = ?rhs")
proof (cases "len v \<ge> n")
  case True
  from fin_vect_dom[OF assms(1) assms(2)] have "dom v = {i. i < len v}" by argo
  also from True have "... = {i. i < n} \<union> {i. n \<le> i \<and> i < len v}" by fastforce
  also from fin_vect_dom[OF cut_vectorI[OF assms(1)] finite_dom_cut, of n] cut_len[OF assms(1) True] have "... = dom (v |x n) \<union> {i. n \<le> i \<and> i < len v}" by presburger
  finally show ?thesis .
next
  case False
  hence v_n_is_None: "v n = None" using fin_vect_None_iff[OF assms] by fastforce
  from False have empty: "{i. n \<le> i \<and> i < len v} = {}" by force
  from v_n_is_None show ?thesis by (simp add: empty, metis cut_def linorder_not_le less_vectorD[OF assms(1)])
qed

subsection "Count Lemmas"

definition count :: "'a vector \<Rightarrow> 'a \<Rightarrow> nat" where
  "count v a = card (v -`{Some a})"

lemma count_alt_def: "count v x = card {i\<in>dom v. v i = Some x}" 
  unfolding dom_def count_def vimage_def by (simp, meson) 

lemma fin_vect_count:
  assumes "vector v" and "finite (dom v)"
  shows "count v x = count (v |x n) x + card {i \<in> dom v. i \<ge> n \<and> v i = Some x}"
proof -
  have h0: "finite {i. i < len v \<and> i < n \<and> v i = Some x}" by fast
  have h1: "finite {i. i < len v \<and> i \<ge> n \<and> v i = Some x}" by fast
  have h2: "{i. i < len v \<and> i < n \<and> v i = Some x} \<inter> {i. i < len v \<and> i \<ge> n \<and> v i = Some x} = {}" by auto
  have h3: "{i. i < len v \<and> v i = Some x} = {i. i < len v \<and> i < n \<and> v i = Some x} \<union> {i. i < len v \<and> i \<ge> n \<and> v i = Some x}" by fastforce
  have h4: "i < n \<Longrightarrow> v i = (v |x n) i" for i unfolding cut_def by auto

  have "count v x = card {i \<in> dom v. v i = Some x}" by (simp only: count_alt_def)
  also have "... = card {i. i < len v \<and> v i = Some x}" by (simp add: fin_vect_dom[OF assms])
  also have "... = card {i. i < len v \<and> i < n \<and> v i = Some x} + card {i. i < len v \<and> i \<ge> n \<and> v i = Some x}" using card_Un_disjoint[OF h0 h1 h2] h3 by argo
  also have "... = card {i. i < len v \<and> i < n \<and> (v |x n) i = Some x} + card {i. i < len v \<and> i \<ge> n \<and> v i = Some x}" by (metis h4)
  also have "... = card {i \<in> dom (v |x n). (v |x n) i = Some x} + card {i \<in> dom v. i \<ge> n \<and> v i = Some x}" by (simp add: fin_vect_dom[OF assms] fin_vect_cut_dom[OF assms])
  finally show ?thesis by (simp add: count_alt_def)
qed

subsection "Map Vector Lemmas"

lemma map_vector_vector:
  shows "vector v \<longleftrightarrow> vector (map_vector f v)"
  unfolding map_vector_def vector_def by simp

lemma map_vector_fin:
  shows "finite (dom v) \<longleftrightarrow> finite (dom (map_vector f v))"
  unfolding map_vector_def by (simp add: finite_dom_iff_fin_vect)

lemma map_vector_len:
  shows "len v = len (map_vector f v)"
  unfolding len_def map_vector_def dom_def by force

lemma map_vector_iff:
  assumes "vector x" and "finite (dom x)"
  shows "((\<forall>i<len x. map_option (f i) (v i) = x i) \<and> (\<forall>i\<ge>len x. v i = None)) \<longleftrightarrow> map_vector f v = x" (is "?lhs1 \<and> ?lhs2 \<longleftrightarrow> ?rhs")
proof (auto, standard)
  assume lhs1: ?lhs1 and lhs2: ?lhs2
  fix i
  show "map_vector f v i = x i"
  proof (cases "i < len x")
    case True
    with lhs1 show ?thesis unfolding map_vector_def by simp
  next
    case False
    with lhs2 have 0: "map_vector f v i = None" unfolding map_vector_def by simp
    from fin_vect_None_iff[OF assms(1,2), of i] lhs1 False have "x i = None" by simp
    with 0 show ?thesis by simp
  qed
next
  fix i
  assume asm1: "x = map_vector f v" and asm2: "i < len (map_vector f v)"
  from assms asm1 asm2 show "map_option (f i) (v i) = map_vector f v i" unfolding map_vector_def by blast
next
  fix i
  assume asm1: "x = map_vector f v" and asm2: "len (map_vector f v) \<le> i"
  from assms asm1 asm2 fin_vect_None_iff show "v i = None" unfolding map_vector_def by fastforce
qed

subsection "Miscellaneous Lemmas"

lemma vector_equ: 
  assumes "vector v" and "finite (dom v)" and "len v = n" and "vector w" and "finite (dom w)" and "len w = n" and "\<forall>i<n. v i = w i"
  shows "v = w"
proof
  fix i
  show "v i = w i"
  proof (cases "i < n")
    case True
    then show ?thesis using assms(7) by blast
  next
    case False
    from False fin_vect_None_iff[OF assms(1,2), of i] assms(3) have 0: "v i = None" by linarith
    from False fin_vect_None_iff[OF assms(4,5), of i] assms(6) have 1: "w i = None" by linarith
    from 0 1 show ?thesis by simp
  qed
qed

lemma zero_one_vector_sum:
  shows "\<lbrakk>vector x; finite (dom x); ran x \<subseteq> {0, 1}\<rbrakk> \<Longrightarrow> (\<Sum>i\<in>{i. i < len x}. N * (the (x i))) = N * (count x 1)"
proof (induction "len x" arbitrary: x)
  case 0
  from 0(1,3) len_def[of x] have "dom x = {}" by force
  then have "count x 1 = 0" using count_alt_def[of x 1] by simp
  with 0 show ?case unfolding count_def by simp
next
  case (Suc n)
  let ?x' = "x |x n"
  from cut_len[OF Suc(3)] Suc(2) have len_x_n: "n = len (x |x n)" by simp
  from len_x_n Suc(1)[OF len_x_n cut_vectorI[OF Suc(3), of n] finite_dom_cut] cut_ran_subset Suc(5) have IH: "(\<Sum>i\<in>{i. i < n}. N * the ((x |x n) i)) = N * count (x |x n) 1" by fastforce
  note semiring_normalization_rules(26)[of N]
  have h0: "{i. i < Suc n} - {n} = {i. i < n}" by fastforce
  have h1: "count (x |x n) 1 + the (x n) = count x 1"
  proof (cases "x n")
    case None
    with fin_vect_Some_iff[OF Suc(3,4), of n] Suc(2) show ?thesis by simp
  next
    case (Some a)
    show ?thesis
    proof (cases a)
      case 0
      have a0: "{i \<in> dom x. i \<ge> n \<and> x i = Some 1} = {}"
      proof 
        show "{i \<in> dom x. i \<ge> n \<and> x i = Some 1} \<subseteq> {}"
        proof
          fix i assume "i \<in> {i \<in> dom x. i \<ge> n \<and> x i = Some 1}" 
          hence a0: "i < Suc n" and a1: "i \<ge> n" and a2: "x i = Some 1" 
            using fin_vect_dom[OF Suc(3,4)] Suc(2) by simp+
          from a0 a1 have a3: "i = n" by linarith
          from 0 a2 a3 Some show "i \<in> {}" by fastforce
        qed
      qed (simp)
      have "count (x |x n) 1 = count (x |x n) 1 + card {i \<in> dom x. i \<ge> n \<and> x i = Some 1}" by (simp only: a0, simp)
      also have "... = count x 1" by (simp only: fin_vect_count[OF Suc(3,4), symmetric])
      finally show ?thesis using 0 Some by simp
    next
      case _: (Suc nat) hence "a \<noteq> 0" by simp
      with Suc(5) Some have a_is_1: "a = 1" unfolding ran_def by blast

      have a0: "{i \<in> dom x. i \<ge> n \<and> x i = Some 1} = {n}"
      proof 
        show "{i \<in> dom x. i \<ge> n \<and> x i = Some 1} \<subseteq> {n}"
        proof
          fix i assume "i \<in> {i \<in> dom x. i \<ge> n \<and> x i = Some 1}" 
          hence a0: "i < Suc n" and a1: "i \<ge> n" and a2: "x i = Some 1" 
            using fin_vect_dom[OF Suc(3,4)] Suc(2) by simp+
          from a0 a1 have a3: "i = n" by linarith
          from a_is_1 a2 a3 Some show "i \<in> {n}" by fastforce
        qed
      qed (simp add: a_is_1 Some Suc(2,3,4) dom_def)
      have "count (x |x n) 1 + 1 = count (x |x n) 1 + card {i \<in> dom x. i \<ge> n \<and> x i = Some 1}" 
        by (simp only: a0, simp)
      also have "... = count x 1" by (simp only: fin_vect_count[OF Suc(3,4), symmetric])
      finally show ?thesis using a_is_1 Some by simp
    qed
  qed

  have "(\<Sum>i\<in>{i. i < Suc n}. N * the (x i)) = (\<Sum>i\<in>{i. i < Suc n} - {n}. N * the (x i)) + (\<Sum>i\<in>{n}. N * the (x i))" by (simp add: sum.subset_diff[of "{n}" "{i. i < Suc n}" "\<lambda>i. N * the (x i)"])
  also have "... = (\<Sum>i\<in>{i. i < n}. N * the (x i)) + (\<Sum>i\<in>{n}. N * the (x i))" by (simp only: h0)
  also have "... = (\<Sum>i\<in>{i. i < n}. N * the (x i)) + (N * the (x n))" by fastforce
  also have "... = (\<Sum>i\<in>{i. i < n}. N * the ((x |x n) i)) + (N * the (x n))" unfolding cut_def by force
  also have "... = N * (count (x |x n) 1 + the (x n))" by (simp add: semiring_normalization_rules IH)
  finally show ?case by (simp only: h1 Suc(2))
qed

lemma zero_one_vector_prod:
  assumes "vector x" and "finite (dom x)" and "ran x \<subseteq> {0, 1}" 
  shows "(\<Prod>i\<in>{i. i < len x}. (N::'a::comm_semiring_1)^(the (x i))) = N^(count x 1)"
  using zero_one_vector_sum[OF assms, of 1] by (simp add: power_sum[symmetric])


end

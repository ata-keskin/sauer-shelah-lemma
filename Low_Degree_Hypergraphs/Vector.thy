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

definition cut :: "'a vector \<Rightarrow> nat \<Rightarrow> 'a vector" where
  "cut v n = (\<lambda>i::nat. if i \<ge> n then None else v i)"

definition map_vector :: "(nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a vector \<Rightarrow> 'b vector" where
  "map_vector f v = (\<lambda>i::nat. map_option (f i) (v i))"

definition vector_of :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a vector" ("/\<langle>_/\<rangle>" [999] 100) where
  "\<langle>f\<rangle> = (\<lambda>i::nat. Some (f i))"

abbreviation enum :: "nat \<Rightarrow> 'a vector \<Rightarrow> 'a" where
  "enum n v \<equiv> the (v n)"

definition n_vectors :: "'a set \<Rightarrow> nat \<Rightarrow> 'a vector set" ("/\<llangle>_/\<rrangle>^_" [0,999] 100) where
  "\<llangle>V\<rrangle>^n = {v::'a vector. vector v \<and> finite (dom v) \<and> len v = n \<and> ran v \<subseteq> V}"

definition set :: "'a vector \<Rightarrow> 'a set" where
 "set v = the ` v ` dom v"

definition prefix :: "'a vector \<Rightarrow> 'a vector \<Rightarrow> bool" (infixl "prefix" 60) where
  "u prefix v \<longleftrightarrow> (\<forall>i\<in>dom u. u i = v i)"

definition suffix :: "'a vector \<Rightarrow> 'a vector \<Rightarrow> bool" (infixl "suffix" 60) where
  "u suffix v \<longleftrightarrow> (\<exists>n. \<forall>i\<ge>n. u i = v (n + i))"

subsection "Basic Properties"

lemma vectorI: 
  assumes "\<forall>i\<ge>n. v i = None" and "\<forall>i<n. v i \<noteq> None"
  shows "vector v"
  by (meson Vector.vector_def assms linorder_not_le order_less_trans)

lemma Some_vectorD: "\<lbrakk>vector v; v n \<noteq> None\<rbrakk> \<Longrightarrow> \<forall>i<n. v i \<noteq> None" unfolding vector_def by blast
lemma None_vectorD: "\<lbrakk>vector v; v n = None\<rbrakk> \<Longrightarrow> \<forall>i\<ge>n. v i = None" unfolding vector_def using order_le_imp_less_or_eq by blast
lemma less_vectorD: "\<lbrakk>vector v; v n \<noteq> None; v m = None\<rbrakk> \<Longrightarrow> n < m" by (meson leI None_vectorD)

\<comment> \<open>Finite vector introduction lemmas\<close>

lemma fin_vect_vectorI: "v \<in> \<llangle>V\<rrangle>^n \<Longrightarrow> vector v" and
      fin_vect_finI:  "v \<in> \<llangle>V\<rrangle>^n \<Longrightarrow> finite (dom v)" and
      fin_vect_lenI:  "v \<in> \<llangle>V\<rrangle>^n \<Longrightarrow> len v = n" and
      fin_vect_ranI:  "v \<in> \<llangle>V\<rrangle>^n \<Longrightarrow> ran v \<subseteq> V" unfolding n_vectors_def by fast+

lemma fin_vect_domI: 
  assumes "v \<in> \<llangle>V\<rrangle>^n"
  shows "dom v = {i. i < n}" 
proof-
  have fin_vect_Some_iff: "(\<exists>x\<in>V. v (i::nat) = Some x) \<longleftrightarrow> i < n" for i
  proof (standard, erule contrapos_pp)
    assume asm: "\<not> i < n"
    have "i \<notin> dom v"
    proof (rule ccontr)
      assume "\<not>i \<notin> dom v" hence "i \<in> dom v" by blast
      with None_vectorD[OF fin_vect_vectorI[OF assms]] have "{k. k \<le> i} \<subseteq> dom v" by fastforce
      from card_mono[OF fin_vect_finI[OF assms] this] card_Collect_le_nat[of i] fin_vect_lenI[OF assms] have "Suc i \<le> n" unfolding len_def by fastforce
      with asm show "False" by simp
    qed
    hence "v i = None" unfolding dom_def by simp
    thus "\<not>(\<exists>x\<in>V. v i = Some x)" by simp
  next
    assume asm: "(i::nat) < n"
    have "i \<in> dom v"
    proof (rule ccontr)
      assume "i \<notin> dom v"
      from less_vectorD[OF fin_vect_vectorI[OF assms]] this have "dom v \<subseteq> {k. k < i}" by blast
      from card_mono[OF _ this] card_Collect_le_nat[of i] fin_vect_lenI[OF assms] asm show "False" unfolding len_def by simp
    qed
    hence "v i \<noteq> None" unfolding dom_def by simp
    hence "(\<exists>x\<in>ran v. v i = Some x)" unfolding ran_def by blast
    with fin_vect_ranI[OF assms] show "\<exists>x\<in>V. v (i::nat) = Some x" by blast
  qed

  from fin_vect_ranI[OF assms, unfolded ran_def] have "(v i \<noteq> None) \<longleftrightarrow> (\<exists>x\<in>V. v i = Some x)" for i by blast
  then have "v i \<noteq> None \<longleftrightarrow> \<not> i \<ge> n" for i using fin_vect_Some_iff by force
  hence s: "v i = None \<longleftrightarrow> i \<ge> n" for i by blast
  thus ?thesis unfolding dom_def by (meson linorder_not_le s)
qed

lemma fin_iff: "finite (dom v) \<longleftrightarrow> (\<exists>n. \<forall>i\<ge>n. (v::'a vector) i = None)"
  by (metis (mono_tags, lifting) dom_def finite_nat_set_iff_bounded linorder_not_le mem_Collect_eq)

lemma infin_vect_domI:
  assumes "vector v" and "infinite (dom v)"
  shows "dom v = UNIV" 
  by (metis UNIV_eq_I assms(1) assms(2) domIff fin_iff None_vectorD)

lemma n_vectorsE: 
  assumes "v \<in> \<llangle>V\<rrangle>^n"
  shows "vector v" and "finite (dom v)" and "len v = n" and "ran v \<subseteq> V"
  using assms by (rule fin_vect_vectorI, rule fin_vect_finI, rule fin_vect_lenI, rule fin_vect_ranI)

lemma domI:
  assumes "\<forall>i<n.\<exists>x\<in>V. v i = Some x" and "\<forall>i\<ge>n. v i = None" 
  shows "dom v = {i. i < n}"

lemma lenI:
  assumes "\<forall>i<n.\<exists>x\<in>V. v i = Some x" and "\<forall>i\<ge>n. v i = None" 
  shows "len v = n"
proof-
    from assms(2) fin_iff have fin_v: "finite (dom v)" by blast
    from assms(1) have "{i. i < n} \<subseteq> dom v" unfolding dom_def by blast
    from card_mono[OF fin_v this] assms(2) show ?thesis
  from len_le[OF assms(1)] len_ge[OF assms(2) this] show ?thesis by fastforce
qed

lemma n_vectors_alt_def: "v \<in> \<llangle>V\<rrangle>^n \<longleftrightarrow> (\<forall>i. v i \<in> Some ` V \<longleftrightarrow> i < n)" (is "?lhs \<longleftrightarrow> ?rhs")
proof 
  assume ?lhs 
  from fin_vect_ranI[OF this] fin_vect_domI[OF this] show ?rhs unfolding ran_def by blast
next
  assume ?rhs
  with vectorI[of n] fin_iff[of v] ranI show ?lhs unfolding n_vectors_def

lemma ranI:
  assumes "\<forall>i\<ge>n::nat. v i = None" and "\<forall>i<n. \<exists>x\<in>V. v i = Some x"
  shows "ran v \<subseteq> V"
proof
  fix x assume "x \<in> ran v"
  then obtain i where asm: "v i = Some x" unfolding ran_def by blast
  show "x \<in> V"
  proof (cases "i < n")
    case True
    with assms(2) asm show ?thesis by fastforce
  next
    case False
    with assms(1) asm show ?thesis by force
  qed
qed

lemma n_vectorsE:
  assumes "\<forall>i\<ge>n. v i = None" and "\<forall>i<n. \<exists>x\<in>V. v i = Some x"
  shows "v \<in> \<llangle>V\<rrangle>^n"
  using vectorI[OF assms(1)] lenI[OF assms(1)] ranI[OF assms] fin_iff assms
  unfolding n_vectors_def by blast

lemma fin_vect_dom_iff:
  shows "dom v = {i. i < n} \<longleftrightarrow> v \<in> \<llangle>UNIV\<rrangle>^n"
proof
  assume dom_v: "dom v = {i. i < n}"
  from vectorI[of n v] dom_def[of v] dom_v have vect_v: "vector v" by (metis (mono_tags, lifting) linorder_not_le mem_Collect_eq)
  from lenI[of n v] dom_def[of v] dom_v have len_v: "len v = n" by (metis (mono_tags, lifting) linorder_not_le mem_Collect_eq)
  from dom_v vect_v len_v finite_Collect_less_nat show "v \<in> \<llangle>UNIV\<rrangle>^n" unfolding n_vectors_def by simp
qed (simp add: fin_vect_domI)

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

\<comment> \<open>Lemmas about the range\<close>

lemma n_vectors_obtain:
  assumes "v \<in> \<llangle>V\<rrangle>^n" and "0 < n"
  obtains x i where "i < n" and "x \<in> V" and "v i = Some x"
proof-
  from fin_vect_lenI[OF assms(1)] assms(2) have "1 \<le> len v" by auto
  with fin_vect_domI[OF assms(1)] obtain x i where v_i_Some: "v i = Some x" unfolding len_def dom_def by fastforce
  with fin_vect_ranI[OF assms(1), unfolded ran_def] have x_in_V: "x \<in> V" by blast
  with v_i_Some fin_vect_Some_iff[OF assms(1)] have i_less_n: "i < n" by blast
  from v_i_Some x_in_V i_less_n that show ?thesis by blast
qed

lemma n_vectors_alt_def: "\<llangle>V\<rrangle>^n = {v. (\<forall>i. (i < n \<longrightarrow> v i \<in> Some ` V) \<and> (i \<ge> n \<longrightarrow> v i = None))}" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof
    fix v assume asm: "v \<in> ?lhs"
    from n_vectorsE[OF asm] fin_vect_None_iff[OF asm] fin_vect_Some_iff[OF asm] image_iff show "v \<in> ?rhs" by blast
  qed
next
  show "?rhs \<subseteq> ?lhs"
  proof
    fix v assume asm: "v \<in> ?rhs"
    from asm show "v \<in> ?lhs" by (subst n_vectorsE, blast+)
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
    from asm finite_Collect_less_nat[of n] fin_vect_dom_iff[of v n] show "v \<in> ?lhs" unfolding n_vectors_def dom_def len_def by fast
  qed
qed

lemma n_vectors_zero: "\<llangle>V\<rrangle>^0 = {Map.empty}" using n_vectors_alt_def[of V 0] by blast

lemma n_vectors_subset: 
  assumes "V \<subseteq> W"
  shows "\<llangle>V\<rrangle>^n \<subseteq> \<llangle>W\<rrangle>^n"
  using assms by (simp add: n_vectors_alt_def, blast)

lemma n_vectors_finite:
  assumes "finite V"
  shows "finite (\<llangle>V\<rrangle>^n)"
  using n_vectors_alt_def2[of V n] finite_set_of_finite_maps[OF finite_Collect_less_nat[of n] assms] by argo

subsection "Cut Lemmas"

lemma cut_vectorI: "vector v \<Longrightarrow> vector (cut v n)" unfolding vector_def by (metis Vector.cut_def dual_order.trans nat_less_le)

lemma fin_cutI: "finite (dom (cut v n))" unfolding cut_def by (auto simp add: fin_iff)

lemma cut_dom: "dom (cut v n) = dom v \<inter> {i. i < n}" unfolding dom_def cut_def by force

lemma fin_vect_cut_dom:
  assumes "v \<in> \<llangle>V\<rrangle>^n"
  shows "(cut v n) \<in> (\<llangle>V\<rrangle>^(min (len v) n))"
  unfolding min_def using fin_vect_domI[OF assms] cut_dom[of v n] fin_vect_lenI[OF assms] by auto

lemma cut_ran_subset: "ran (cut v n) \<subseteq> ran v" unfolding ran_def cut_def by auto

lemma len_cut_le: 
  shows "len (cut v n) \<le> n"
proof-
  from cut_dom[of v n] have "dom (cut v n) \<subseteq> {i. i < n}" by blast
  from card_mono[OF _ this] card_Collect_less_nat[of n] show ?thesis unfolding len_def by fastforce
qed

lemma len_cut: 
  assumes "\<exists>k\<ge>n. v \<in> \<llangle>V\<rrangle>^k"
  shows "len (cut v n) = n"
proof (cases "finite (dom v)")
  case True
  from assms obtain k where fin_vect: "v \<in> \<llangle>V\<rrangle>^k" and k_ge_n: "k \<ge> n" by blast 
  from cut_dom[of v n] fin_vect_cut_dom[OF ] have "len (cut v n) = card {i. i < min k n}"
  also from assms have "... = card {i. i < n}" sorry
  also from card_Collect_less_nat have "... = n" by blast
  finally show ?thesis .
next
  case False
  from assms infinite_len_0[OF False] have "n = 0" sorry
  then show ?thesis unfolding dom_def len_def cut_def by simp
qed

lemma fin_vect_dom_cutI: 
  assumes "v\<in>\<llangle>V\<rrangle>^n"
  shows "dom v = dom (cut v k) \<union> {i. k \<le> i \<and> i < len v}" (is "?lhs = ?rhs")
proof (cases "len v \<ge> k")
  case True
  from fin_vect_domI[OF assms] fin_vect_lenI[OF assms] have "dom v = {i. i < len v}" by auto
  also from True have "... = {i. i < k} \<union> {i. k \<le> i \<and> i < len v}" by fastforce
  also from fin_vect_domI[OF assms] fin_vect_lenI[OF assms] len_cut have "... = dom (cut v k) \<union> {i. k \<le> i \<and> i < len v}" sorry
  finally show ?thesis .
next
  case False
  hence v_n_is_None: "v n = None" using fin_vect_None_iff[OF assms] sorry
  from False have empty: "{i. n \<le> i \<and> i < len v} = {}" by force
  from v_n_is_None show ?thesis by (simp add: empty, metis cut_def linorder_not_le less_vectorD[OF assms(1)])
qed

lemma 

subsection "Count Lemmas"

definition count :: "'a vector \<Rightarrow> 'a \<Rightarrow> nat" where
  "count v a = card (v -`{Some a})"

lemma count_alt_def: "count v x = card {i\<in>dom v. v i = Some x}" 
  unfolding dom_def count_def vimage_def by (simp, meson) 

lemma fin_vect_count:
  assumes "v\<in>\<llangle>V\<rrangle>^n"
  shows "count v x = count (cut v n) x + card {i \<in> dom v. i \<ge> n \<and> v i = Some x}"
proof -
  have h0: "finite {i. i < len v \<and> i < n \<and> v i = Some x}" by fast
  have h1: "finite {i. i < len v \<and> i \<ge> n \<and> v i = Some x}" by fast
  have h2: "{i. i < len v \<and> i < n \<and> v i = Some x} \<inter> {i. i < len v \<and> i \<ge> n \<and> v i = Some x} = {}" by auto
  have h3: "{i. i < len v \<and> v i = Some x} = {i. i < len v \<and> i < n \<and> v i = Some x} \<union> {i. i < len v \<and> i \<ge> n \<and> v i = Some x}" by fastforce
  have h4: "i < n \<Longrightarrow> v i = (cut v n) i" for i unfolding cut_def by auto

  have "count v x = card {i \<in> dom v. v i = Some x}" by (simp only: count_alt_def)
  also have "... = card {i. i < len v \<and> v i = Some x}" apply (simp add: fin_vect_domI[OF assms] dom_def len_def) sorry
  also have "... = card {i. i < len v \<and> i < n \<and> v i = Some x} + card {i. i < len v \<and> i \<ge> n \<and> v i = Some x}" using card_Un_disjoint[OF h0 h1 h2] h3 by argo
  also have "... = card {i. i < len v \<and> i < n \<and> (cut v n) i = Some x} + card {i. i < len v \<and> i \<ge> n \<and> v i = Some x}" by (metis h4)
  also have "... = card {i \<in> dom (cut v n). (cut v n) i = Some x} + card {i \<in> dom v. i \<ge> n \<and> v i = Some x}" by (simp add: fin_vect_dom[OF assms] fin_vect_cut_dom[OF assms])
  finally show ?thesis by (simp add: count_alt_def)
qed

subsection "Map Vector Lemmas"

lemma map_vector_vector:
  shows "vector v \<longleftrightarrow> vector (map_vector f v)"
  unfolding map_vector_def vector_def by simp

lemma map_vector_fin:
  shows "finite (dom v) \<longleftrightarrow> finite (dom (map_vector f v))"
  unfolding map_vector_def by (simp add: fin_iff)

lemma map_vector_len:
  shows "len v = len (map_vector f v)"
  unfolding len_def map_vector_def dom_def by force

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
    from fin_vect_None_iff[OF assms, of i] lhs1 False have "x i = None" by simp
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

lemma map_vector_btw:
  assumes "x \<in> \<llangle>U::'a set\<rrangle>^n"
  shows "map_vector f x \<in> \<llangle>\<Union>f_i \<in> (image f \<nat>). image f_i (ran x)\<rrangle>^n"
  using assms

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
  let ?x' = "cut x n"
  from len_cut[OF Suc(3)] Suc(2) have len_x_n: "n = len (cut x n)" by simp
  from len_x_n Suc(1)[OF len_x_n cut_vectorI[OF Suc(3), of n] fin_cutI] cut_ran_subset Suc(5) have IH: "(\<Sum>i\<in>{i. i < n}. N * the ((cut x n) i)) = N * count (cut x n) 1" by fastforce
  note semiring_normalization_rules(26)[of N]
  have h0: "{i. i < Suc n} - {n} = {i. i < n}" by fastforce
  have h1: "count (cut x n) 1 + the (x n) = count x 1"
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
      have "count (cut x n) 1 = count (cut x n) 1 + card {i \<in> dom x. i \<ge> n \<and> x i = Some 1}" by (simp only: a0, simp)
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
      have "count (cut x n) 1 + 1 = count (cut x n) 1 + card {i \<in> dom x. i \<ge> n \<and> x i = Some 1}" 
        by (simp only: a0, simp)
      also have "... = count x 1" by (simp only: fin_vect_count[OF Suc(3,4), symmetric])
      finally show ?thesis using a_is_1 Some by simp
    qed
  qed

  have "(\<Sum>i\<in>{i. i < Suc n}. N * the (x i)) = (\<Sum>i\<in>{i. i < Suc n} - {n}. N * the (x i)) + (\<Sum>i\<in>{n}. N * the (x i))" by (simp add: sum.subset_diff[of "{n}" "{i. i < Suc n}" "\<lambda>i. N * the (x i)"])
  also have "... = (\<Sum>i\<in>{i. i < n}. N * the (x i)) + (\<Sum>i\<in>{n}. N * the (x i))" by (simp only: h0)
  also have "... = (\<Sum>i\<in>{i. i < n}. N * the (x i)) + (N * the (x n))" by fastforce
  also have "... = (\<Sum>i\<in>{i. i < n}. N * the ((cut x n) i)) + (N * the (x n))" unfolding cut_def by force
  also have "... = N * (count (cut x n) 1 + the (x n))" by (simp add: semiring_normalization_rules IH)
  finally show ?case by (simp only: h1 Suc(2))
qed

lemma zero_one_vector_prod:
  assumes "vector x" and "finite (dom x)" and "ran x \<subseteq> {0, 1}" 
  shows "(\<Prod>i\<in>{i. i < len x}. (N::'a::comm_semiring_1)^(the (x i))) = N^(count x 1)"
  using zero_one_vector_sum[OF assms, of 1] by (simp add: power_sum[symmetric])

end

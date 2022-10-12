
theory Lemma
  imports Main "HOL-Probability.Probability_Mass_Function" "HOL-Probability.Product_PMF"
begin

fun random_subset :: "'a set \<Rightarrow> real \<Rightarrow> ('a \<Rightarrow> bool) pmf" where
  "random_subset V p = Pi_pmf V False (\<lambda>_. bernoulli_pmf p)"

fun random_subsets :: "'a set \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> ('a \<Rightarrow> bool)) pmf" where
  "random_subsets V p n = Pi_pmf {i::nat. i \<le> n} (\<lambda>_. False) (\<lambda>_. random_subset V p)"

fun intersect :: "'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> nat" where
  "intersect U = (\<lambda>S. card {u\<in>U. S u})"

fun intersect2 :: "'a set \<Rightarrow> (nat \<Rightarrow> ('a \<Rightarrow> bool)) \<Rightarrow> (nat \<Rightarrow> nat)" where
  "intersect2 U = (\<lambda>f i. card {u\<in>U. (f i) u})"

fun equ :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool" where
  "equ n x y \<longleftrightarrow> (\<forall>i \<le> n. x i = y i)"

lemma 
  assumes [simp]: "T = (random_subsets V p n)" and "0 \<le> p" and "p \<le> 1" and "finite V" and "U \<subseteq> V" and "U' \<subseteq> V" 
                  and "d = card U" and "d = card U'" and "r = card (U \<inter> U')" and "range x = {0, 1}"
  shows "measure_pmf.prob T {Ss. equ n (intersect2 U Ss) x \<and> equ n (intersect2 U' Ss) x} = ((1 - p) ^ ((2 * d - r) * n)) * ((p * r)/(1-p) + ((p * (d-r))/(1-p))^2)^(card (x -`{1}))"
proof -

  note finite_U = finite_subset[OF assms(5) assms(4)]
  note finite_U' = finite_subset[OF assms(6) assms(4)]

  have first_step: "measure_pmf.prob T {Ss. equ n (intersect2 U Ss) x \<and> equ n (intersect2 U' Ss) x} =
         (\<Prod>i\<in>{i. i\<le>n}. measure_pmf.prob (map_pmf (\<lambda>f. f i) T) {S. intersect U S = x i \<and> intersect U' S = x i})"
  proof -
    have Pi_set: "{Ss. equ n (intersect2 U Ss) x \<and> equ n (intersect2 U' Ss) x}
             = (\<Pi> i\<in>{i. i\<le>n}. {S. intersect U S = x i \<and> intersect U' S = x i})" by auto
    have project: "i \<le> n \<Longrightarrow> (map_pmf (\<lambda>f. f i) T) = (random_subset V p)" for i 
    by (simp add: Pi_pmf_component)
  
    have "measure_pmf.prob T {Ss. equ n (intersect2 U Ss) x \<and> equ n (intersect2 U' Ss) x} =
          measure_pmf.prob T (\<Pi> i\<in>{i. i\<le>n}. {S. intersect U S = x i \<and> intersect U' S = x i})" by (simp only: Pi_set)
    also have "... = (\<Prod>i\<in>{i. i\<le>n}. measure_pmf.prob (random_subset V p) {S. intersect U S = x i \<and> intersect U' S = x i})" by (simp add: measure_Pi_pmf_Pi)
    also have "... = (\<Prod>i\<in>{i. i\<le>n}. measure_pmf.prob (map_pmf (\<lambda>f. f i) T) {S. intersect U S = x i \<and> intersect U' S = x i})" using project by simp
    finally show ?thesis .
  qed

  have second_step: "measure_pmf.prob (random_subset V p) {S. intersect U S = x i \<and> intersect U' S = x i} 
        = (1 - p) ^ (2 * d - r) * ((p * r)/(1-p) + ((p * (d-r))/(1-p))^2)^(x i)" for i 
  proof (cases "x i")
    case 0
    then have "measure_pmf.prob (random_subset V p) {S. intersect U S = x i \<and> intersect U' S = x i}
    =  measure_pmf.prob (random_subset V p) {S. card {u\<in>U. S u} = 0 \<and> card {u\<in>U'. S u} = 0}" by simp
    also have "... = measure_pmf.prob (Pi_pmf V False (\<lambda>_. bernoulli_pmf p)) {S. card {u\<in>U. S u} = 0 \<and> card {u\<in>U'. S u} = 0}" by simp

    also have "... = (\<Prod>v\<in>V. measure_pmf.prob (bernoulli_pmf p) {v\<in>(U \<union> U')})" sorry
    also have "... = (\<Prod>v\<in>V. sum (pmf (bernoulli_pmf p)) {v\<in>(U \<union> U')})" sorry
    also have "... = (\<Prod>v\<in>V. pmf (bernoulli_pmf p) (v\<in>(U \<union> U')))" by simp
    also have "... = (1 - p) ^ (2 * d - r)" sorry
    finally show ?thesis using 0 by simp
  next
    case (Suc nat)
    with assms(10) have "x i = 1" by (metis empty_iff insert_iff nat.distinct(1) rangeI)
    then show ?thesis sorry
  qed
  
  show ?thesis sorry
qed




end
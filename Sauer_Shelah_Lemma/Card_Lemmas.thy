(*  Title:      Card_Lemmas.thy
    Author:     Ata Keskin, TU München
*)

theory Card_Lemmas
  imports Main
begin

section "Lemmas involving the cardinality of sets"

lemma card_diff: 
  assumes "finite A"
  shows "card A = card (A - B) + card (A \<inter> B)"
proof -
  from assms have fin0: "finite (A - B)" and fin1: "finite (A \<inter> B)" by blast+
  have A_equ: "A = (A - B) \<union> (A \<inter> B)" and disjoint: "(A - B) \<inter> (A \<inter> B) = {}" by blast+
  from card_Un_disjoint[OF fin0 fin1 disjoint] A_equ show ?thesis by argo
qed


lemma card_Int_copy:
  assumes "finite X" and "A \<union> B \<subseteq> X" and "\<exists>f. inj_on f (A \<inter> B) \<and> (A \<union> B) \<inter> (f ` (A \<inter> B)) = {} \<and> f ` (A \<inter> B) \<subseteq> X"
  shows "card A + card B \<le> card X"
proof -
  from rev_finite_subset[OF assms(1), of A] rev_finite_subset[OF assms(1), of B] assms(2) 
  have finite_A: "finite A" and finite_B: "finite B" by blast+
  then have finite_A_Un_B: "finite (A \<union> B)" and finite_A_Int_B: "finite (A \<inter> B)" by blast+
  from assms(3) obtain f where f_inj_on: "inj_on f (A \<inter> B)" and f_disjnt: "(A \<union> B) \<inter> (f ` (A \<inter> B)) = {}" and f_imj_in: "f ` (A \<inter> B) \<subseteq> X" by blast
  from finite_A_Int_B have finite_f_img: "finite (f ` (A \<inter> B))" by blast
  from assms(2) f_imj_in have union_in: "(A \<union> B) \<union> f ` (A \<inter> B) \<subseteq> X" by blast
  
  from card_Un_Int[OF finite_A finite_B] have "card A + card B = card (A \<union> B) + card (A \<inter> B)" .
  also from card_image[OF f_inj_on] have "... = card (A \<union> B) + card (f ` (A \<inter> B))" by presburger
  also from card_Un_disjoint[OF finite_A_Un_B finite_f_img f_disjnt] have "... = card ((A \<union> B) \<union> f ` (A \<inter> B))" by argo
  also from card_mono[OF assms(1) union_in] have "... \<le> card X" by blast
  finally show ?thesis .
qed

lemma card_ge_0:
  assumes "A \<noteq> {}" and "finite A"
  shows "0 < card A"
proof -
  from assms(1) have "{} \<subset> A" by blast
  from psubset_card_mono[OF assms(2) this] show ?thesis by force
qed

lemma finite_diff_not_empty: 
  assumes "finite Y" and "card Y < card X"
  shows "X - Y \<noteq> {}"
proof
  assume "X - Y = {}"
  hence "X \<subseteq> Y" by simp
  from card_mono[OF assms(1) this] assms(2) show False by linarith
qed

lemma finite_subset_exists:
  assumes "finite A"
  shows "k \<le> card A \<Longrightarrow> \<exists>S\<in>Pow A. card S = k \<and> finite S"
proof (induction k)
  case 0
  then show ?case by force
next
  case (Suc k)
  from Suc(2) have k_le_card_A: "k \<le> card A" by linarith
  from Suc(1)[OF k_le_card_A] rev_finite_subset[OF assms] obtain S
    where S_subset_A: "S \<subseteq> A" and card_S_is_k: "card S = k" and finite_S: "finite S" by blast
  from Suc(2) card_S_is_k have "card S < card A" by linarith
  from card_psubset[OF assms S_subset_A this] obtain x where x_is_new: "x \<in> A - S" by blast
  let ?S' = "S \<union> {x}"
  from S_subset_A x_is_new have "?S' \<subseteq> A" by blast
  moreover
  from x_is_new card_S_is_k finite_S have "card ?S' = Suc k" by auto
  ultimately show ?case using rev_finite_subset[OF assms] by blast
qed

lemma difference_element_exists:
  fixes F :: "'a set set"
  assumes "2 \<le> card F"
  shows "\<exists>x\<in> \<Union>F. x \<notin> \<Inter>F"
proof -
  from assms card_le_Suc_iff[of 1 F] obtain A F' where 0: "F = insert A F'" and 1: "A \<notin> F'" and 2: "1 \<le> card F'" by auto
  from 2 card_le_Suc_iff[of 0 F'] obtain B F'' where 3: "F' = insert B F''" by auto
  from 1 3 have A_noteq_B: "A \<noteq> B" by blast
  from 0 3 have A_in_F: "A \<in> F" and B_in_F: "B \<in> F" by blast+
  from A_noteq_B have "(A - B) \<union> (B - A) \<noteq> {}" by simp
  with A_in_F B_in_F show ?thesis by blast
qed

end
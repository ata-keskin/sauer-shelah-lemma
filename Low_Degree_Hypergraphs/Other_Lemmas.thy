theory Other_Lemmas
  imports Main "HOL-Analysis.Analysis"
begin

lemma sum_square_zero_one:
  assumes "finite I" and "\<forall>i. f i \<in> {0,1::real}"
  shows "(\<Sum>i\<in>I. f i)^2 = (\<Sum>j\<in>I. \<Sum>i\<in>I. (f j) * (f i))"
using assms proof (induction I)
  case empty
  then show ?case by simp
next
  case (insert x I)
  then show ?case
  proof (cases "f x = 0")
    case True
    with insert show ?thesis by fastforce
  next
    case False with assms(2) have f_x_is_1: "f x = 1" by blast
    have first_step: "(\<Sum>i\<in>insert x I. f i)^2 = (\<Sum>i\<in>insert x I. f i) * (\<Sum>j\<in>insert x I. f j)" by algebra
    also from insert(1,2) f_x_is_1 have "... = (1 + (\<Sum>i\<in>I. f i)) * (1 + (\<Sum>j\<in>I. f j))" by force
    also have "... = (1 + (\<Sum>i\<in>I. f i)) + (\<Sum>i\<in>I. f i) + (\<Sum>j\<in>I. f j)^2" by algebra
    also from insert(3)[OF insert(4)] have "... = (1 + (\<Sum>i\<in>I. f i)) + (\<Sum>i\<in>I. f i) + (\<Sum>j\<in>I. \<Sum>i\<in>I. f j * f i)" by presburger
    also have "... = (1 + (\<Sum>i\<in>I. f i)) + (\<Sum>i\<in>I. f i) + (\<Sum>j\<in>I. f j * (\<Sum>i\<in>I. f i))" by (simp add: sum_distrib_left)
    also from insert(1,2) f_x_is_1 have "... = (\<Sum>i\<in>insert x I. f i) + (\<Sum>j\<in>insert x I. f j * (\<Sum>i\<in>I. f i))" by force
    also have "... = (\<Sum>i\<in>insert x I. f i) + (\<Sum>i\<in>I. (\<Sum>j\<in>insert x I. f j) * f i)" by (metis sum_distrib_left sum_distrib_right)
    also from insert(1,2) f_x_is_1 have "... = (\<Sum>i\<in>insert x I. (\<Sum>j\<in>insert x I. f i * f j))" by (metis calculation first_step sum_product)
    finally show ?thesis .
  qed
qed
end
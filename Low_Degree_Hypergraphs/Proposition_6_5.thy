theory Proposition_6_5
  imports Main Lemma_6_3
begin

(* We can also replace these definitions by using https://www.isa-afp.org/theories/undirected_graph_theory/ *)
type_synonym 'a graph = "('a set) \<times> ('a set set)"
abbreviation vertices where "vertices \<equiv> fst"
abbreviation edges where "edges \<equiv> snd"
abbreviation well_formed where "well_formed G \<equiv> edges G \<subseteq> Pow (vertices G)"

definition regular :: "nat \<Rightarrow> 'a graph \<Rightarrow> bool" (infixl "regular" 80) where 
  "d regular G = (\<forall>e\<in>edges G. card e = d)"

proposition proposition_6_5: 
  assumes "0 \<le> p" and "p < 1" and "finite (vertices G)" and "d regular G"
          and vect_x: "vector x" and fin_x: "finite (dom x)" and len_x: "len x = n" and ran_x: "ran x \<subseteq> {0, 1}"
        shows "measure_pmf.prob (pmf_vector (random_subset V p) n) {T. ran T \<subseteq> power_set V \<and> x \<notin> {map_vector ((\<lambda>_ S. card {u\<in>U. S u})) T | U. U \<in> edges G}} 
            \<le> measure_pmf.expectation (map_pmf exp P) Q - 1"
proof -
  term P

end
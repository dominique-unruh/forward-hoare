theory Demo_Hoare
  imports Main Forward_Hoare
begin

type_synonym var = String.literal
type_synonym mem = \<open>var \<Rightarrow> int\<close>
datatype instruction = Add var var | Set var int | Guess var
type_synonym "program" = "instruction list"

fun semantics1 :: "instruction \<Rightarrow> mem \<Rightarrow> mem set" where
  "semantics1 (Set x i) m = {m(x:=i)}"
| "semantics1 (Add x y) m = {m(x:=m x + m y)}"
| "semantics1 (Guess x) m = {m(x:=i)| i. True}"

fun semantics :: "program \<Rightarrow> mem \<Rightarrow> mem set" where
  "semantics [] m = {m}"
| "semantics (c#p) m = (\<Union>m'\<in>semantics1 c m. semantics p m')"

type_synonym "invariant" = "mem \<Rightarrow> bool"

definition "hoare" :: "invariant \<Rightarrow> program \<Rightarrow> invariant \<Rightarrow> bool" where
  "hoare A p B \<longleftrightarrow> (\<forall>m. A m \<longrightarrow> (\<exists>m'\<in>semantics p m. B m'))"


fun postcondition_trivial :: "instruction \<Rightarrow> invariant \<Rightarrow> invariant" where
  "postcondition_trivial (Set x i) I = (\<lambda>m. m x = i \<and> (\<exists>j. I (m(x:=j))))"
| "postcondition_trivial (Guess x) I = (\<lambda>m. \<exists>j. I (m(x:=j)))"
| "postcondition_trivial (Add x y) I = (\<lambda>m. I (m(x:=m x - m y)))"

fun postcondition_pick :: "instruction \<Rightarrow> int \<Rightarrow> invariant \<Rightarrow> invariant" where
  "postcondition_pick (Guess x) i I = (\<lambda>m. m x = i \<and> (\<exists>j. I (m(x:=j))))"
| "postcondition_pick _ _ _ = undefined"

lemma semantics_seq: "semantics (p@q) m = 
  (\<Union>m'\<in>semantics p m. semantics q m')"
  by (induction p arbitrary: m, auto)

lemma hoare_seq:
  assumes "hoare A p B"
  assumes "hoare B q C"
  shows "hoare A (p@q) C"
proof (unfold hoare_def, auto)
  fix m
  assume "A m"
  with assms(1) obtain m' where "B m'" and m': "m' \<in> semantics p m"
    apply atomize_elim unfolding hoare_def by auto
  with assms(2) obtain m'' where "C m''" and m'': "m'' \<in> semantics q m'"
    apply atomize_elim unfolding hoare_def by auto
  from m' m'' have "m'' \<in> semantics (p@q) m"
    unfolding semantics_seq by auto
  with \<open>C m''\<close> show "\<exists>m''\<in>semantics (p@q) m. C m''"
    by auto
qed

lemma hoare_seq':
  assumes "hoare A p B"
  assumes "hoare B q C"
  assumes "pq = p @ q"
  shows "hoare A pq C"
  unfolding assms(3) using assms(1-2) by (rule hoare_seq) 


definition "pc_imp pc1 pc2 \<longleftrightarrow> (\<forall>m. pc1 m \<longrightarrow> pc2 m)" for pc1 pc2 :: "invariant"

lemma pc_impI[intro]: "(\<And>m. pc1 m \<Longrightarrow> pc2 m) \<Longrightarrow> pc_imp pc1 pc2"
  unfolding pc_imp_def by auto

lemma pc_impD[dest]: "pc_imp pc1 pc2 \<Longrightarrow> pc1 m \<Longrightarrow> pc2 m"
  unfolding pc_imp_def by auto

lemma hoare_conseq:
  assumes "pc_imp A A'"
  assumes "pc_imp B' B"
  assumes "hoare A' p B'"
  shows "hoare A p B"
  using assms unfolding hoare_def pc_imp_def by blast

lemma hoare_conseq':
  assumes "hoare A' p' B'"
  assumes "pc_imp A A'"
  assumes "pc_imp B' B"
  assumes "p = p'"
  shows "hoare A p B"
  using assms unfolding hoare_def pc_imp_def by blast


lemma hoare_skip[simp]: "hoare A [] A"
  unfolding hoare_def by auto

lemma hoare_cons: 
  assumes "hoare A [c] B"
  assumes "hoare B p C"
  shows "hoare A (c#p) C"
  using assms unfolding hoare_def apply auto by metis

lemma hoareI:
  assumes "\<And>m. A m \<Longrightarrow> Bex (semantics p m) B"
  shows "hoare A p B"
  unfolding hoare_def using assms by simp

lemma valid_Add:
  assumes "B \<equiv> postcondition_trivial (Add x y) A"
  defines "p \<equiv> [Add x y]"
  assumes distinct: "x \<noteq> y"
  shows "hoare A p B"
  apply (rule hoareI)
  unfolding assms(1-2) using distinct by simp


lemma valid_Set:
  assumes "B \<equiv> postcondition_trivial (Set x i) A"
  defines "p \<equiv> [Set x i]"
  shows "hoare A p B"
  apply (rule hoareI)
  unfolding assms
  apply simp
  by (metis fun_upd_triv)

lemma valid_Guess_trivial:
  assumes "B \<equiv> postcondition_trivial (Guess x) A"
  defines "p == [Guess x]"
  shows "hoare A p B"
  apply (rule hoareI)
  unfolding assms
  apply simp
  by (metis fun_upd_triv)

lemma valid_Guess_pick:
  assumes "B \<equiv> postcondition_pick (Guess x) i A"
  defines "p == [Guess x]"
  shows "hoare A p B"
  apply (rule hoareI)
  unfolding assms
  apply (rule bexI[of _ "_(x := i)"])
  apply auto
  by (metis fun_upd_triv)

lemmas valid = valid_Set valid_Guess_pick valid_Guess_trivial valid_Add



definition "independent_of (B::invariant) (x::var) = (\<forall>m1 m2. (\<forall>y\<noteq>x. m1 y = m2 y) \<longrightarrow> B m1 = B m2)"
lemma independent_ofI: 
  assumes "\<And>m1 m2. (\<And>y. y\<noteq>x \<Longrightarrow> m1 y = m2 y) \<Longrightarrow> B m1 = B m2"
  shows "independent_of B x"
  unfolding independent_of_def using assms by metis

lemma newvalue_Set:
  assumes "invariant \<equiv> postcondition_trivial (Set x i) A"
  shows "pc_imp invariant (\<lambda>m. m x = i)"
  unfolding assms
  by (rule pc_impI; simp)

lemma newvalue_Guess: 
  assumes "invariant \<equiv> postcondition_pick (Guess x) i A"
  shows "pc_imp invariant (\<lambda>m. m x = i)"
  unfolding assms
  by (rule pc_impI; simp)

lemmas newvalue = newvalue_Set newvalue_Guess

lemma unchanged_Guess_trivial: 
  assumes "invariant \<equiv> postcondition_trivial (Guess x) A"
  assumes indep: "independent_of B x"
  assumes imp: "\<And>m. A m \<Longrightarrow> B m"
  shows "pc_imp invariant B"
  unfolding assms(1)
  apply (rule pc_impI; simp)
  using indep imp unfolding independent_of_def apply auto
  by (metis fun_upd_def)+

lemma unchanged_Guess_pick: 
  assumes "invariant \<equiv> postcondition_pick (Guess x) i A"
  assumes indep: "independent_of B x"
  assumes imp: "\<And>m. A m \<Longrightarrow> B m"
  shows "pc_imp invariant B"
  unfolding assms(1)
  apply (rule pc_impI; simp)
  using indep imp unfolding independent_of_def apply auto
  by (metis fun_upd_def)+

lemma unchanged_Add: 
  assumes "invariant \<equiv> postcondition_trivial (Add x y) A"
  assumes indep: "independent_of B x"
  assumes xy: "x \<noteq> y"
  assumes imp: "\<And>m. A m \<Longrightarrow> B m"
  shows "pc_imp invariant B"
  unfolding assms
  apply (rule pc_impI)
  using indep imp xy unfolding independent_of_def apply auto
  by (metis fun_upd_def)

lemma unchanged_Set: 
  assumes "invariant \<equiv> postcondition_trivial (Set x i) A"
  assumes indep: "independent_of B x"
  assumes imp: "\<And>m. A m \<Longrightarrow> B m"
  shows "pc_imp invariant B"
  unfolding assms(1)
  apply (rule pc_impI)
  using indep imp unfolding independent_of_def apply auto
  by (metis fun_upd_def)

lemmas unchanged = unchanged_Guess_pick unchanged_Guess_trivial unchanged_Add unchanged_Set

lemma wp_Add: 
  assumes "invariant \<equiv> postcondition_trivial (Add x y) A"
  assumes distinct: "x \<noteq> y"
  assumes imp: "\<And>m. A m \<Longrightarrow> B (m(x:=m x + m y))"
  shows "pc_imp invariant B"
  unfolding assms(1)
  apply (rule pc_impI)
  using distinct apply simp apply (drule imp)
  by auto

lemma wp_Set:
  assumes "invariant \<equiv> postcondition_trivial (Set x i) A"
  assumes imp: "\<And>m. A m \<Longrightarrow> B (m(x:=i))"
  shows "pc_imp invariant B"
  unfolding assms(1)
  apply (rule pc_impI)
  apply simp
  using imp
  apply auto
  apply (drule imp)
  by auto

lemmas wp = wp_Add wp_Set

lemma append_aux1:
  assumes "xs = ys @ zs"
  shows "x#xs = (x#ys) @ zs"
  using assms by auto

lemma append_aux2:
  shows "xs = [] @ xs"
  by auto



ML_file "demo_hoare.ML"


end
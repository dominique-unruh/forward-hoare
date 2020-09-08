theory PRHL
  imports CryptHOL.CryptHOL Forward_Hoare Variables
begin

no_notation m_inv ("inv\<index> _" [81] 80)

instance unit :: CARD_1
  apply intro_classes by auto

section \<open>Programs\<close>

lemma less_eq_card_trans[trans]: 
  assumes "less_eq_card A B" and "less_eq_card B C"
  shows "less_eq_card A C"
proof -
  from assms obtain fAB fBC 
    where inj_fAB: "inj_on fAB A" and range_fAB: "range fAB \<subseteq> B" and inj_fBC: "inj_on fBC B" and range_fBC: "range fBC \<subseteq> C"
    apply atomize_elim unfolding less_eq_card_def by auto
  define f where "f = fBC o fAB"
  have "inj_on f A"
    unfolding f_def
    using inj_fAB apply (rule comp_inj_on)
    using range_fAB inj_fBC
    by (meson UNIV_I image_subset_iff inj_on_subset)
  moreover have "range f \<subseteq> C"
    unfolding f_def using range_fBC by auto
  ultimately show ?thesis
    unfolding less_eq_card_def
    by auto
qed

lemma less_eq_card_spmf[simp]: "less_eq_card (UNIV::'val set) (UNIV::'val spmf set)"
  unfolding less_eq_card_def apply (rule exI[of _ return_spmf])
  by (simp add: inj_on_def)

type_synonym ('mem,'var) expression = \<open>'mem \<Rightarrow> 'var\<close>
type_synonym 'mem untyped_expression = \<open>('mem,'mem) expression\<close>
type_synonym 'mem untyped_spmf_expression = \<open>('mem,'mem spmf) expression\<close>

datatype 'mem instruction = 
  SetRaw "'mem untyped_var" "'mem untyped_expression"
  | SampleRaw "'mem untyped_var" "'mem untyped_spmf_expression"
  | IfThenElse "('mem,bool) expression" "'mem instruction list" "'mem instruction list"

definition Set :: "('mem,'val) var \<Rightarrow> ('mem,'val) expression \<Rightarrow> 'mem instruction" where
  "Set x e = SetRaw (mk_var_untyped x) ((some_embedding::'val\<Rightarrow>'mem) o e)"

definition Sample :: "('mem,'val) var \<Rightarrow> ('mem,'val spmf) expression \<Rightarrow> 'mem instruction" where
  "Sample x e = SampleRaw (mk_var_untyped x) (map_spmf (some_embedding::'val\<Rightarrow>'mem) o e)"

definition Assert :: "('mem,bool) expression \<Rightarrow> 'mem instruction" where
  "Assert e = Sample unit_var (\<lambda>m. assert_spmf (e m))"

type_synonym 'mem "program" = "'mem instruction list"

section \<open>Semantics\<close>

fun semantics1 :: "'mem instruction \<Rightarrow> 'mem \<Rightarrow> 'mem spmf"
  and semantics :: "'mem program \<Rightarrow> 'mem \<Rightarrow> 'mem spmf" where
  "semantics1 (SetRaw x e) m = return_spmf (update_untyped_var x (e m) m)"
| "semantics1 (SampleRaw x e) m = map_spmf (\<lambda>a. update_untyped_var x a m) (e m)"
| "semantics1 (IfThenElse c P Q) m = (if (c m) then semantics P m else semantics Q m)"

| "semantics [] m = return_spmf m"
| semantics_Cons: "semantics (c#p) m = bind_spmf (semantics1 c m) (semantics p)"


lemma semantics1_Set[simp]:
  fixes x :: "('mem,'val) var" and a :: 'val
  shows "semantics1 (Set x e) m = return_spmf (update_var x (e m) m)"
  unfolding Set_def apply simp
  by (rule update_untyped_var)

lemma semantics1_Sample[simp]:
  fixes x :: "('mem,'val) var" and a :: 'val
  shows "semantics1 (Sample x e) m = map_spmf (\<lambda>a. update_var x a m) (e m)"
  unfolding Sample_def apply simp
  by (smt map_spmf_cong o_def spmf.map_comp update_untyped_var)

lemma semantics1_Assert[simp]:
  fixes m :: 'mem
  shows "semantics1 (Assert e) m = (if e m then return_spmf m else return_pmf None)"
  unfolding Assert_def by (simp add: map_spmf_idI) 

lemma semantics1_Set_invalid:
  fixes x :: "('mem,'val) var" and a :: 'val
  (* assumes "\<not> has_variables TYPE('mem) TYPE('val)" *)
  assumes "\<not> valid_var x"
  shows "semantics1 (Set x e) m = return_spmf m"
  unfolding invalid_is_dummy_var[OF assms] Set_def
  by (simp add: update_untyped_var)

lemma semantics1_Sample_invalid:
  fixes x :: "('mem,'val) var" and a :: 'val
  (* assumes "\<not> has_variables TYPE('mem) TYPE('val)" *)
  assumes "\<not> valid_var x"
  shows "semantics1 (Sample x e) m = scale_spmf (weight_spmf (e m)) (return_spmf m)"
  unfolding invalid_is_dummy_var[OF assms] Sample_def
  by (auto simp: map_spmf_conv_bind_spmf bind_spmf_const update_untyped_var spmf.map_comp o_def)

lemma semantics_Nil[simp]: "semantics [] = return_spmf"
  by auto

type_synonym 'mem "invariant" = "'mem \<Rightarrow> bool"
type_synonym ('m1,'m2) "rinvariant" = "'m1 \<Rightarrow> 'm2 \<Rightarrow> bool"

definition "hoare" :: "'mem invariant \<Rightarrow> 'mem program \<Rightarrow> 'mem invariant \<Rightarrow> bool" where
  "hoare A p B \<longleftrightarrow> (\<forall>m. A m \<longrightarrow> pred_spmf B (semantics p m))"

lemma hoareI: 
  assumes "\<And>m. A m \<Longrightarrow> pred_spmf B (semantics p m)"
  shows "hoare A p B"
  using assms unfolding hoare_def by simp

(* definition "is_coupling \<mu> \<mu>1 \<mu>2 \<longleftrightarrow> map_spmf fst \<mu> = \<mu>1 \<and> map_spmf snd \<mu> = \<mu>2" *)

definition "rhoare" :: "('m1,'m2) rinvariant \<Rightarrow> 'm1 program \<Rightarrow> 'm2 program \<Rightarrow> ('m1,'m2) rinvariant \<Rightarrow> bool" where
  "rhoare A p1 p2 B \<longleftrightarrow> (\<forall>m1 m2. A m1 m2 \<longrightarrow> rel_spmf B (semantics p1 m1) (semantics p2 m2))"

section \<open>Support for reasoning\<close>

definition postcondition_default :: "'mem program \<Rightarrow> 'mem invariant \<Rightarrow> 'mem invariant" where
  "postcondition_default p I m \<longleftrightarrow> (\<exists>m'. I m' \<and> m \<in> set_spmf (semantics p m'))"

definition postcondition_default2 :: "'mem1 program \<Rightarrow> 'mem2 program \<Rightarrow> ('mem1,'mem2) rinvariant \<Rightarrow> ('mem1,'mem2) rinvariant" where
  "postcondition_default2 = (\<lambda>p1 p2 I m1 m2.
      \<exists>m1' m2'. I m1' m2' \<and> m1 \<in> set_spmf (semantics p1 m1')
                          \<and> m2 \<in> set_spmf (semantics p2 m2'))"

definition postcondition_rnd :: "('mem1 \<Rightarrow> 'mem2 \<Rightarrow> ('x1*'x2) spmf) \<Rightarrow> ('mem1,'x1) var \<Rightarrow> ('mem2,'x2) var \<Rightarrow> ('mem1,'mem2) rinvariant \<Rightarrow> ('mem1,'mem2) rinvariant" where
  "postcondition_rnd j x1 x2 I m1 m2 = 
    (\<exists>m1' m2'. I m1' m2' \<and> (m1,m2) \<in> 
      (\<lambda>(v1,v2). (update_var x1 v1 m1', update_var x2 v2 m2')) ` set_spmf (j m1' m2'))"

lemma postcondition_default_valid:
  "hoare A p (postcondition_default p A)"
  unfolding postcondition_default_def hoare_def
  using pred_spmf_def by blast

lemma coupling_exists:
  assumes "weight_spmf \<mu>1 = weight_spmf \<mu>2"
  shows "\<exists>\<mu>. map_spmf fst \<mu> = \<mu>1 \<and> map_spmf snd \<mu> = \<mu>2"
proof (cases "weight_spmf \<mu>1 = 0")
  case True
  with assms have "weight_spmf \<mu>2 = 0"
    by simp
  with True have \<mu>1: "\<mu>1 = return_pmf None" and \<mu>2: "\<mu>2 = return_pmf None"
    using weight_spmf_eq_0 by auto
  show ?thesis
    apply (rule exI[of _ "return_pmf None"])
    by (auto simp: \<mu>1 \<mu>2)
next
  case False
  define w \<mu> 
    where "w = weight_spmf \<mu>1"
      and "\<mu> = scale_spmf (inverse w) (pair_spmf \<mu>1 \<mu>2)"
  have w_def': "w = weight_spmf \<mu>2"
    using assms w_def by blast
  have [simp]: "w > 0" and [simp]: "w \<le> 1"
    unfolding w_def using False
    using zero_less_measure_iff apply blast
    by (simp add: weight_spmf_le_1)
  have *: "inverse w * max 0 (min (inverse w) w) = 1"
    using \<open>w > 0\<close> \<open>w \<le> 1\<close>
    by (smt left_inverse one_le_inverse)
    
  have "map_spmf fst \<mu> = \<mu>1"
    unfolding \<mu>_def map_scale_spmf map_fst_pair_spmf
    apply (subst scale_scale_spmf)
    unfolding w_def[symmetric] w_def'[symmetric] *
    by simp

  moreover have "map_spmf snd \<mu> = \<mu>2"
    unfolding \<mu>_def map_scale_spmf map_snd_pair_spmf
    apply (subst scale_scale_spmf)
    unfolding w_def[symmetric] w_def'[symmetric] *
    by simp

  ultimately show ?thesis 
    by auto
qed

(* lemma coupling_supp:
  assumes "is_coupling \<mu> \<mu>1 \<mu>2"
  shows "set_spmf \<mu> \<subseteq> set_spmf \<mu>1 \<times> set_spmf \<mu>2"
  using assms
  by (auto simp add: is_coupling_def rev_image_eqI) *)

lemma weight_semantics_Nil: "weight_spmf (semantics [] m) = 1"
  by simp

lemma weight_semantics_Set_cons: "weight_spmf (semantics (Set x e # P) m) = 
  weight_spmf (semantics P (update_var x (e m) m))"
  by simp

lemma same_weight1:
  assumes "\<lbrakk>SOLVER same_weight_tac\<rbrakk> weight_spmf (semantics p m1) = 1"
  assumes "\<lbrakk>SOLVER same_weight_tac\<rbrakk> weight_spmf (semantics q m2) = 1"
  shows "weight_spmf (semantics p m1) = weight_spmf (semantics q m2)"
  using assms by simp

lemma weight1_Set:
  shows "weight_spmf (semantics1 (Set x e) m) = 1"
  by simp

lemma weight1_cons:
  assumes "\<lbrakk>SOLVER same_weight_tac\<rbrakk> weight_spmf (semantics1 i m) = 1"
  assumes "\<And>m. \<lbrakk>SOLVER same_weight_tac\<rbrakk> weight_spmf (semantics p m) = 1"
  shows "weight_spmf (semantics (i#p) m) = 1"
  using assms by (auto simp: weight_bind_spmf o_def)

lemma weight1_if:
  assumes "\<lbrakk>SOLVER same_weight_tac\<rbrakk> weight_spmf (semantics p m) = 1"
  assumes "\<lbrakk>SOLVER same_weight_tac\<rbrakk> weight_spmf (semantics q m) = 1"
  shows "weight_spmf (semantics1 (IfThenElse c p q) m) = 1"
  using assms by auto


lemma postcondition_default2_valid:
  assumes "\<lbrakk>SOLVER same_weight_tac?\<rbrakk> (\<And>m1 m2. A m1 m2 \<Longrightarrow> weight_spmf (semantics p m1) = weight_spmf (semantics q m2))"
  shows "rhoare A p q (postcondition_default2 p q A)"
proof -
  obtain \<mu> 
    where \<mu>1: "map_spmf fst (\<mu> m1 m2) = semantics p m1"
      and \<mu>2: "map_spmf snd (\<mu> m1 m2) = semantics q m2" 
    if "A m1 m2" for m1 m2
    apply atomize_elim 
    using coupling_exists[OF assms[unfolded SOLVE_WITH_def, rule_format]]
    by (auto simp: all_conj_distrib[symmetric] intro!: choice)

  have supp: "m1' \<in> set_spmf (semantics p m1)" 
     "m2' \<in> set_spmf (semantics q m2)"
    if "(m1', m2') \<in> set_spmf (\<mu> m1 m2)" and "A m1 m2" for m1' m2' m1 m2
    unfolding \<mu>1[OF \<open>A m1 m2\<close>, symmetric] \<mu>2[OF \<open>A m1 m2\<close>, symmetric]
    using that by force+

  show ?thesis
    by (auto simp: postcondition_default2_def rhoare_def case_prod_beta pred_spmf_def intro!: rel_spmfI \<mu>1 \<mu>2 supp)
qed

lemma postcondition_rnd_valid:
  (* assumes p_def: "p = ([Sample x1 e1], [Sample x2 e2])" *)
  (* assumes "\<And>m1 m2. A m1 m2 \<Longrightarrow> map_spmf fst (\<mu> m1 m2) = semantics (fst p) m1" *)
  (* assumes "\<And>m1 m2. A m1 m2 \<Longrightarrow> map_spmf snd (\<mu> m1 m2) = semantics (snd p) m2" *)
  (* assumes "\<And>m1 m2. A m1 m2 \<Longrightarrow> set_spmf (\<mu> m1 m2) \<subseteq> j m1 m2" *)
  assumes fst: "\<And>m1 m2. A m1 m2 \<Longrightarrow> map_spmf fst (\<mu> m1 m2) = e1 m1"
  assumes snd: "\<And>m1 m2. A m1 m2 \<Longrightarrow> map_spmf snd (\<mu> m1 m2) = e2 m2"
  shows "rhoare A [Sample x1 e1] [Sample x2 e2] (postcondition_rnd \<mu> x1 x2 A)"
proof (unfold rhoare_def, rule, rule, rule)
  fix m1 m2 assume A: "A m1 m2"
  define \<mu>' where "\<mu>' = map_spmf (\<lambda>(v1, v2). (update_var x1 v1 m1, update_var x2 v2 m2)) (\<mu> m1 m2)"

  have "(m1', m2') \<in> set_spmf \<mu>' \<Longrightarrow> postcondition_rnd \<mu> x1 x2 A m1' m2'" for m1' m2'
    unfolding postcondition_rnd_def \<mu>'_def
    apply (rule exI[of _ m1], rule exI[of _ m2])
    using \<open>A m1 m2\<close> by auto

  moreover have "map_spmf fst \<mu>' = semantics [Sample x1 e1] m1"
    unfolding \<mu>'_def 
    by (simp add: fst[OF A, symmetric] spmf.map_comp o_def case_prod_beta)

  moreover have "map_spmf snd \<mu>' = semantics [Sample x2 e2] m2"
    unfolding \<mu>'_def 
    by (simp add: snd[OF A, symmetric] spmf.map_comp o_def case_prod_beta)

  ultimately show "rel_spmf (postcondition_rnd \<mu> x1 x2 A) (semantics [Sample x1 e1] m1) (semantics [Sample x2 e2] m2)"
    by (rule rel_spmfI[where pq=\<mu>'])
qed

abbreviation (input) "independentL_of e x \<equiv> (\<And>m2. independent_of (\<lambda>m1. e m1 m2) x)"
abbreviation (input) "independentR_of e x \<equiv> (\<And>m1. independent_of (\<lambda>m2. e m1 m2) x)"

definition "independent_of_prog e P \<longleftrightarrow> (\<forall>m. \<forall>m'\<in>set_spmf (semantics P m). e m = e m')"
abbreviation (input) "independentL_of_prog e x \<equiv> (\<And>m2. independent_of_prog (\<lambda>m1. e m1 m2) x)"
abbreviation (input) "independentR_of_prog e x \<equiv> (\<And>m1. independent_of_prog (\<lambda>m2. e m1 m2) x)"


(* axiomatization independent_of :: "('mem \<Rightarrow> 'a) \<Rightarrow> ('mem,'b) var \<Rightarrow> bool" *)
(* definition "independent_of (B::'mem expression) (x::'mem var) = (\<forall>m1 m2. (\<forall>y\<noteq>x. m1 y = m2 y) \<longrightarrow> B m1 = B m2)" *)

(* lemma independent_ofI[intro]: 
  assumes "\<And>m1 m2. (\<And>y. y\<noteq>x \<Longrightarrow> eval_var y m1 = eval_var y m2) \<Longrightarrow> B m1 = B m2"
  shows "independent_of B x"
   *)
(*  unfolding independent_of_def using assms by metis *)

lemma semantics1_Set_Sample:
  "semantics1 (Set x e) = semantics1 (Sample x (\<lambda>m. return_spmf (e m)))"
  by auto


definition "instructions_commute a b \<longleftrightarrow> semantics [a,b] = semantics [b,a]"

lemma instructions_commute_cong:
  "semantics1 a = semantics1 a' \<Longrightarrow> semantics1 b = semantics1 b'
  \<Longrightarrow> instructions_commute a b = instructions_commute a' b'"
  unfolding instructions_commute_def by (auto simp: semantics_Cons[abs_def])

lemma commute_indep_Sample_Sample:
  fixes a :: "('mem,'a) var" and b :: "('mem,'b) var"
  assumes "independent_of f a"
  assumes "independent_of e b"
  assumes "independent_vars a b"
  shows "instructions_commute (Sample a e) (Sample b f)"
proof -
  have \<open>semantics [Sample a e, Sample b f] mem = semantics [Sample b f, Sample a e] mem\<close> for mem
  proof -
    have "f (update_var a x mem) = f mem" for x
      by (rule assms(1)[unfolded independent_of_def, rule_format, symmetric])
    then have 1: "semantics [Sample a e, Sample b f] mem
      = map_spmf (%(x,y). update_var b y (update_var a x mem)) (pair_spmf (e mem) (f mem))"
      by (simp add: bind_map_spmf o_def pair_spmf_alt_def map_bind_spmf
          map_spmf_conv_bind_spmf[symmetric] spmf.map_comp)
    have "e (update_var b x mem) = e mem" for x
      by (rule assms(2)[unfolded independent_of_def, rule_format, symmetric])
    then have 2: "semantics [Sample b f, Sample a e] mem
      = map_spmf (%(x,y). update_var a x (update_var b y mem)) (pair_spmf (e mem) (f mem))"
      apply (subst pair_commute_spmf)
      by (simp add: bind_map_spmf o_def pair_spmf_alt_def map_bind_spmf
          map_spmf_conv_bind_spmf[symmetric] spmf.map_comp)
    show "semantics [Sample a e, Sample b f] mem = semantics [Sample b f, Sample a e] mem"
      unfolding 1 2
      using assms(3) unfolding independent_vars_def by simp
  qed
  then show ?thesis
    unfolding instructions_commute_def by auto
qed

lemma commute_indep_Set_Sample:
  fixes a :: "('mem,'a) var" and b :: "('mem,'b) var"
  assumes "independent_of f a"
  assumes "independent_of e b"
  assumes "independent_vars a b"
  shows "instructions_commute (Set a e) (Sample b f)"
  apply (subst instructions_commute_cong)
    apply (rule semantics1_Set_Sample, rule refl)
  using assms(1) _ assms(3) apply (rule commute_indep_Sample_Sample)
  apply (rule independent_of_split[OF _ assms(2)])
  by simp

lemma commute_indep_Sample_Set:
  fixes a :: "('mem,'a) var" and b :: "('mem,'b) var"
  assumes "independent_of f a"
  assumes "independent_of e b"
  assumes "independent_vars a b"
  shows "instructions_commute (Sample a e) (Set b f)"
  apply (subst instructions_commute_cong)
    apply (rule refl, rule semantics1_Set_Sample)
  using _ assms(2-3) apply (rule commute_indep_Sample_Sample)
  apply (rule independent_of_split[OF _ assms(1)])
  by simp

lemma commute_indep_Assert_Set:
  fixes a :: "('mem,'a) var" and b :: "('mem,'b) var"
  assumes "independent_of e b"
  shows "instructions_commute (Assert e) (Set b f)"
  unfolding Assert_def
  apply (rule commute_indep_Sample_Set)
    apply simp
  apply (rule independent_of_split[OF _ assms(1)])
  by simp_all

(* TODO: generalize using independent_of_prog or similar? Or add cases for Sample? *)
lemma commute_indep_Set_Set:
  fixes a :: "('mem,'a) var" and b :: "('mem,'b) var"
  assumes "independent_of f a"
  assumes "independent_of e b"
  assumes "independent_vars a b"
  shows "instructions_commute (Set a e) (Set b f)"
  apply (subst instructions_commute_cong)
    apply (rule refl, rule semantics1_Set_Sample)
  using _ assms(2-3) apply (rule commute_indep_Set_Sample)
  apply (rule independent_of_split[OF _ assms(1)])
  by simp

lemma insert_into_ordered_singleton_aux:
  "semantics [i] = semantics [i]"
  by simp

lemma insert_into_ordered_prepend_aux:
  "semantics (i#is) = semantics (i#is)"
  by simp

lemma insert_into_ordered_aux:
  fixes a b :: "'mem instruction"
  assumes "instructions_commute a b"
  assumes "semantics (a#c) = semantics ac"
  shows "semantics (a#b#c) = semantics (b#ac)"
proof -
  define seq where "seq x y m = x m \<bind> y" for x y :: "'mem\<Rightarrow>'mem spmf" and m
  note [simp] = seq_def[abs_def] semantics.simps[abs_def]
  write seq (infixl ";;" 70)
  have "semantics (a#b#c) = (semantics1 a;; semantics1 b);; semantics c"
    by simp
  also have "semantics1 a;; semantics1 b = semantics1 b;; semantics1 a"
    using assms(1) by (simp add: instructions_commute_def)
  also have "(semantics1 b;; semantics1 a);; semantics c = semantics1 b;; (semantics1 a;; semantics c)"
    by auto
  also have "semantics1 a;; semantics c = semantics ac"
    using assms(2) by simp
  also have "semantics1 b;; semantics ac = semantics (b#ac)"
    by auto
  finally show ?thesis
    by -
qed

lemma join_with_ordered_empty_aux:
  "semantics ([] @ prog) = semantics prog"
  by simp

lemma join_with_ordered_aux:
  assumes "semantics (p@s) = semantics q"
  assumes "semantics (i#q) = semantics r"
  shows "semantics ((i#p)@s) = semantics r"
  using assms by (simp add: semantics.simps[abs_def] o_def)

(* lemma sort_program_empty_aux:
  "semantics [] = semantics []"
  by simp

lemma sort_program_aux:
  assumes "semantics p = semantics q"
  assumes "semantics (i#q) = semantics r"
  shows "semantics (i#p) = semantics r"
  using assms by (simp add: semantics.simps[abs_def] o_def) *)

lemma sort_program_aux:
  "semantics (p@[]) = semantics q \<Longrightarrow> semantics p = semantics q"
  by simp

lemma semantics_seq:
  "semantics (p@q) = (\<lambda>m. semantics p m \<bind> semantics q)"
  apply (rule ext, rename_tac m)
  apply (induction p; simp)
  by presburger

lemma hoare_seq:
  assumes "hoare A p B"
  assumes "hoare B q C"
  shows "hoare A (p@q) C"
  using assms unfolding hoare_def semantics_seq
  using spmf_pred_mono_strong by force

lemma rhoare_seq:
  assumes "rhoare A p p' B"
  assumes "rhoare B q q' C"
  shows "rhoare A (p@q) (p'@q') C"
  using assms unfolding rhoare_def semantics_seq
  using rel_spmf_bindI by blast

lemma append_conv0: "[] @ z \<equiv> z"
  by simp

lemma append_conv1: "(x#y) @ z \<equiv> x # (y@z)"
  by simp

lemma join_hoare:
  assumes "hoare invariant1 (p12@p23) invariant3"
  assumes "p12 @ p23 \<equiv> p13"
  assumes "semantics p13 = semantics srt"
  shows "hoare invariant1 srt invariant3"
  using assms unfolding hoare_def by simp

lemma join_rhoare:
  assumes "rhoare invariant1 (p12@p23) (p12'@p23') invariant3"
  assumes "p12 @ p23 \<equiv> p13"
  assumes "p12' @ p23' \<equiv> p13'"
  assumes "semantics p13 = semantics srt"
  assumes "semantics p13' = semantics srt'"
  shows "rhoare invariant1 srt srt' invariant3"
  using assms unfolding rhoare_def by simp


(* We use \<longrightarrow> and not \<Longrightarrow> in invariant implications because
   otherwise applying a rule to an invariant implication subgoal 
   leaves too much freedom to Isabelle and Isabelle is not forced to
   match the "invariant m" part of the conclusion of the rule
 *)

lemma wp_default2[hoare_wp add]:
  fixes x :: "('mem,'val) var"
  assumes "invariant \<equiv> postcondition_default2 p1 p2 A"
  assumes "\<And>m1 m2. A m1 m2 \<Longrightarrow> A' m1 m2"
  assumes "\<lbrakk>SOLVER wp_tac\<rbrakk> \<And>m2. \<forall>m1. postcondition_default p1 (\<lambda>m1. B m1 m2) m1 \<longrightarrow> C m1 m2"
  assumes "\<lbrakk>SOLVER wp_tac\<rbrakk> \<And>m1. \<forall>m2. postcondition_default p2 (A' m1) m2 \<longrightarrow> B m1 m2"
  shows "\<forall>m1 m2. invariant m1 m2 \<longrightarrow> C m1 m2"
  using assms(2-4) unfolding assms(1) postcondition_default2_def postcondition_default_def 
  apply auto by metis

(* lemma wp_generic[hoare_wp add]:
  fixes x :: "('mem,'val) var"
  assumes "invariant \<equiv> postcondition_default2 p1 p2 A"
  assumes "\<And>m1 m2. A m1 m2 \<Longrightarrow> A' m1 m2"
  assumes "\<lbrakk>SOLVER wp_tac\<rbrakk> \<forall>m1 m2. postcondition_default2 p1 p2 A' m1 m2 \<longrightarrow> B m1 m2"
  shows "\<forall>m1 m2. invariant m1 m2 \<longrightarrow> B m1 m2"
  using assms(2,3) unfolding assms(1) postcondition_default2_def 
  apply auto by metis *)

lemma wp_default[hoare_wp add]:
  fixes x :: "('mem,'val) var"
  assumes "invariant \<equiv> postcondition_default p A"
  assumes "\<And>m. A m \<Longrightarrow> A' m"
  assumes "\<lbrakk>SOLVER wp_tac\<rbrakk> \<forall>m. postcondition_default p A' m \<longrightarrow> B m"
  shows "\<forall>m. invariant m \<longrightarrow> B m"
  using assms(2,3) unfolding assms(1) postcondition_default_def by auto

lemma wp_rnd[hoare_wp add]:
  assumes "invariant \<equiv> postcondition_rnd \<mu> x y A"
  assumes "\<And>m1 m2. A m1 m2 \<Longrightarrow> (\<forall>(a,b)\<in>set_spmf (\<mu> m1 m2). B (update_var x a m1) (update_var y b m2))"
  shows "\<forall>m1 m2. invariant m1 m2 \<longrightarrow> B m1 m2"
  using assms unfolding postcondition_rnd_def
  apply auto by blast

(* lemma wp_Set_cons1:
  assumes "\<lbrakk>SOLVER wp_tac\<rbrakk> \<forall>mem1 mem2. postcondition_default2 p1 p2 M mem1 mem2 \<longrightarrow> B mem1 mem2"
  shows "\<forall>mem1 mem2. postcondition_default2 (Set x e # p1) p2 (\<lambda>m1 m2. M (update_var x (e m1) m1) m2) mem1 mem2 \<longrightarrow> B mem1 mem2"
  using assms unfolding postcondition_default2_def
  by auto *)

(* lemma wp_Sample_cons1:
  assumes "\<lbrakk>SOLVER wp_tac\<rbrakk> \<forall>mem1 mem2. postcondition_default2 p1 p2 M mem1 mem2 \<longrightarrow> B mem1 mem2"
  shows "\<forall>mem1 mem2. postcondition_default2 (Sample x e # p1) p2
               (\<lambda>m1 m2. \<forall>a\<in>set_spmf (e m1). M (update_var x a m1) m2) mem1 mem2 \<longrightarrow> B mem1 mem2"
  using assms unfolding postcondition_default2_def apply auto by blast *)

(* lemma wp_Set_cons2:
  assumes "\<lbrakk>SOLVER wp_tac\<rbrakk> \<forall>mem1 mem2. postcondition_default2 p1 p2 M mem1 mem2 \<longrightarrow> B mem1 mem2"
  shows "\<forall>mem1 mem2. postcondition_default2 p1 (Set x e # p2) (\<lambda>m1 m2. M m1 (update_var x (e m2) m2)) mem1 mem2 \<longrightarrow> B mem1 mem2"
  using assms unfolding postcondition_default2_def
  by auto *)

(* lemma wp_Sample_cons2:
  assumes "\<lbrakk>SOLVER wp_tac\<rbrakk> \<forall>mem1 mem2. postcondition_default2 p1 p2 M mem1 mem2 \<longrightarrow> B mem1 mem2"
  shows "\<forall>mem1 mem2. postcondition_default2 p1 (Sample x e # p2)
               (\<lambda>m1 m2. \<forall>a\<in>set_spmf (e m2). M m1 (update_var x a m2)) mem1 mem2 \<longrightarrow> B mem1 mem2"
  using assms unfolding postcondition_default2_def apply auto by blast *)

(* lemma wp_skip12:
  shows "\<forall>mem1 mem2. postcondition_default2 [] [] B mem1 mem2 \<longrightarrow> B mem1 mem2"
  unfolding postcondition_default2_def
  by auto *)

lemma wp_Set_cons:
  assumes "\<lbrakk>SOLVER wp_tac\<rbrakk> \<forall>mem. postcondition_default p M mem \<longrightarrow> B mem"
  shows "\<forall>mem. postcondition_default (Set x e # p) (\<lambda>m. M (update_var x (e m) m)) mem \<longrightarrow> B mem"
  using assms unfolding postcondition_default_def
  by auto

lemma wp_Sample_cons:
  assumes "\<lbrakk>SOLVER wp_tac\<rbrakk> \<forall>mem. postcondition_default p M mem \<longrightarrow> B mem"
  shows "\<forall>mem. postcondition_default (Sample x e # p) 
    (\<lambda>m. \<forall>a\<in>set_spmf (e m). M (update_var x a m)) mem \<longrightarrow> B mem"
  using assms unfolding postcondition_default_def by auto

lemma wp_IfThenElse_cons:
  assumes "\<lbrakk>SOLVER wp_tac\<rbrakk> \<forall>mem. postcondition_default r B mem \<longrightarrow> C mem"
  assumes "\<lbrakk>SOLVER wp_tac\<rbrakk> \<forall>mem. postcondition_default p Ap mem \<longrightarrow> B mem"
  assumes "\<lbrakk>SOLVER wp_tac\<rbrakk> \<forall>mem. postcondition_default q Aq mem \<longrightarrow> B mem"
  shows "\<forall>mem. postcondition_default (IfThenElse c p q # r)
    (\<lambda>mem. if c mem then Ap mem else Aq mem) mem \<longrightarrow> C mem"
  using assms unfolding postcondition_default_def apply auto by blast

lemma wp_skip:
  shows "\<forall>mem. postcondition_default [] B mem \<longrightarrow> B mem"
  unfolding postcondition_default_def
  by auto

lemma independent_of_prog_append:
  assumes "independent_of_prog A P"
  assumes "independent_of_prog A Q"
  shows "independent_of_prog A (P@Q)"
  using assms
  by (auto simp add: o_def independent_of_prog_def semantics_seq)

lemma independent_of_prog_Set:
  assumes "independent_of A x"
  shows "independent_of_prog A [Set x e]"
  using assms unfolding independent_of_prog_def independent_of_def
  by simp

lemma independent_of_prog_Set_cons:
  assumes "independent_of A x"
  assumes "independent_of_prog A P"
  shows "independent_of_prog A (Set x e # P)"
  apply (rule independent_of_prog_append[where P="[_]", simplified])
   apply (rule independent_of_prog_Set)
  using assms by -

lemma independent_of_prog_Sample:
  assumes "independent_of A x"
  shows "independent_of_prog A [Sample x e]"
  using assms unfolding independent_of_prog_def independent_of_def
  by simp

lemma independent_of_prog_Sample_cons:
  assumes "independent_of A x"
  assumes "independent_of_prog A P"
  shows "independent_of_prog A (Sample x e # P)"
  apply (rule independent_of_prog_append[where P="[_]", simplified])
   apply (rule independent_of_prog_Sample)
  using assms by -

lemma independent_of_prog_empty:
  shows "independent_of_prog A []"
  unfolding independent_of_prog_def by simp

lemma untouched[hoare_untouched add]: 
  fixes x :: "('mem,'val) var"
  assumes "invariant \<equiv> postcondition_default P A"
  assumes imp: "\<forall>m. A m \<longrightarrow> B m"
  assumes indep: "\<lbrakk>SOLVER independence_tac\<rbrakk> independent_of_prog B P"
  shows "\<forall>m. invariant m \<longrightarrow> B m"
  using imp indep
  unfolding assms(1) postcondition_default_def 
            independent_of_prog_def
  by auto

lemma untouchedLR[hoare_untouched add]: 
  fixes x :: "('mem,'val) var"
  assumes "invariant \<equiv> postcondition_default2 P1 P2 A"
  assumes imp: "\<forall>m1 m2. A m1 m2 \<longrightarrow> B m1 m2"
  assumes indepL: "\<lbrakk>SOLVER independence_tac\<rbrakk> PROP independentL_of_prog B P1"
  assumes indepR: "\<lbrakk>SOLVER independence_tac\<rbrakk> PROP independentR_of_prog B P2"
  shows "\<forall>m1 m2. invariant m1 m2 \<longrightarrow> B m1 m2"
  using imp indepL indepR
  unfolding assms(1) postcondition_default2_def independent_of_prog_def
  apply auto by blast


lemma untouched_rnd[hoare_untouched add]: 
  fixes x :: "('mem,'val) var"
  assumes invariant_def: "invariant \<equiv> postcondition_rnd \<mu> x y A"
  assumes imp: "\<forall>m1 m2. A m1 m2 \<longrightarrow> B m1 m2"
  assumes indepL: "\<lbrakk>SOLVER independence_tac\<rbrakk> PROP independentL_of B x"
  assumes indepR: "\<lbrakk>SOLVER independence_tac\<rbrakk> PROP independentR_of B y"
  shows "\<forall>m1 m2. invariant m1 m2 \<longrightarrow> B m1 m2"
proof (rule+)
  fix m1 m2 assume "invariant m1 m2"
  then obtain m1' m2' where "A m1' m2'" 
    and in_supp: "(m1, m2) \<in> (\<lambda>(v1, v2). (update_var x v1 m1', update_var y v2 m2')) 
                                   ` set_spmf (\<mu> m1' m2')"
    unfolding invariant_def postcondition_rnd_def apply atomize_elim by auto
  from in_supp obtain v1 v2 where (* "(v1,v2) \<in> set_spmf (\<mu> m1' m2')" 
    and *) v1: "m1 = update_var x v1 m1'" and v2: "m2 = update_var y v2 m2'"
    by auto
  from \<open>A m1' m2'\<close> have \<open>B m1' m2'\<close>
    using imp by simp
  then have \<open>B (update_var x v1 m1') m2'\<close>
    using indepL by (auto simp: independent_of_def)
  then have \<open>B m1 m2'\<close>
    using v1 by simp
  then have \<open>B m1 (update_var y v2 m2')\<close>
    using indepR by (auto simp: independent_of_def)
  then show \<open>B m1 m2\<close>
    using v2 by simp
qed

lemma mk_invariant_consequence1:
  assumes "A \<equiv> B"
  shows "\<forall>m. A m \<longrightarrow> B m"
  using assms by auto

lemma mk_invariant_consequence2:
  assumes "A \<equiv> B"
  shows "\<forall>m1 m2. A m1 m2 \<longrightarrow> B m1 m2"
  using assms by auto

lemma split_invariant_implication_conj1:
  assumes "\<forall>m. A m \<longrightarrow> (B m \<and> B' m)"
  shows "\<forall>m. A m \<longrightarrow> B m" and "\<forall>m. A m \<longrightarrow> B' m"
  using assms by auto

lemma split_invariant_implication_conj2:
  assumes "\<forall>m1 m2. A m1 m2 \<longrightarrow> (B m1 m2 \<and> B' m1 m2)"
  shows "\<forall>m1 m2. A m1 m2 \<longrightarrow> B m1 m2" and "\<forall>m1 m2. A m1 m2 \<longrightarrow> B' m1 m2"
  using assms by auto

lemma split_invariant_implication_all1:
  assumes "\<forall>m. A m \<longrightarrow> (\<forall>x. B x m)"
  shows "\<forall>m. A m \<longrightarrow> B x m"
  using assms by auto

lemma split_invariant_implication_all2:
  assumes "\<forall>m1 m2. A m1 m2 \<longrightarrow> (\<forall>x. B x m1 m2)"
  shows "\<forall>m1 m2. A m1 m2 \<longrightarrow> B x m1 m2"
  using assms by auto

lemma split_invariant_implication_ball1:
  assumes "\<forall>m. A m \<longrightarrow> (\<forall>x\<in>M m. B x m)"
  shows "\<forall>m. A m \<longrightarrow> (x \<in> M m \<longrightarrow> B x m)"
  using assms by auto

lemma split_invariant_implication_ball2:
  assumes "\<forall>m1 m2. A m1 m2 \<longrightarrow> (\<forall>x\<in>M m1 m2. B x m1 m2)"
  shows "\<forall>m1 m2. A m1 m2 \<longrightarrow> (x \<in> M m1 m2 \<longrightarrow> B x m1 m2)"
  using assms by auto


lemma split_invariant_implication_imp1:
  assumes "\<forall>m. A m \<longrightarrow> (C \<longrightarrow> B m)"
  shows "C \<Longrightarrow> \<forall>m. A m \<longrightarrow> B m"
  using assms by auto

lemma split_invariant_implication_imp2:
  assumes "\<forall>m1 m2. A m1 m2 \<longrightarrow> (C \<longrightarrow> B m1 m2)"
  shows "C \<Longrightarrow> \<forall>m1 m2. A m1 m2 \<longrightarrow> B m1 m2"
  using assms by auto

definition spmf_sums :: "'a spmf \<Rightarrow> 'a spmf \<Rightarrow> 'a spmf \<Rightarrow> bool" where
  "spmf_sums a b c = (\<forall>x. spmf a x + spmf b x = spmf c x)"

lemma spmf_sumsI:
  assumes "\<And>x. spmf a x + spmf b x = spmf c x"
  shows "spmf_sums a b c"
  unfolding spmf_sums_def using assms by simp

lemma spmf_density: "measure_spmf a = density (count_space UNIV) (spmf a)"
proof (rule measure_eqI, simp)
  fix A
  have "emeasure (measure_spmf a) A =  (\<integral>\<^sup>+x\<in>A. ennreal (spmf a x)\<partial>count_space UNIV)"
    by (metis Pow_UNIV UNIV_I nn_integral_indicator nn_integral_measure_spmf sets_count_space sets_measure_spmf)
  also have "\<dots> = emeasure (density (count_space UNIV) (\<lambda>x. ennreal (spmf a x))) A"
    apply (subst emeasure_density)
    by auto
  finally show "emeasure (measure_spmf a) A =
      emeasure (density (count_space UNIV) (\<lambda>x. ennreal (spmf a x))) A"
    by -
qed

lemma spmf_sums_bind1:
  fixes a b c :: "'a spmf" and d :: "'a \<Rightarrow> 'b spmf"
  assumes "spmf_sums a b c"
  shows "spmf_sums (a \<bind> d) (b \<bind> d) (c \<bind> d)"
proof (rule spmf_sumsI)
  fix x
  have "ennreal (spmf (a \<bind> d) x) + ennreal (spmf (b \<bind> d) x)
    = (\<integral>\<^sup>+ y. ennreal (spmf (d y) x) \<partial>measure_spmf a) +
      (\<integral>\<^sup>+ y. ennreal (spmf (d y) x) \<partial>measure_spmf b)"
    by (auto simp: ennreal_spmf_bind)
  also have "\<dots> = 
    (\<integral>\<^sup>+ y. ennreal (spmf (d y) x) \<partial>density (count_space UNIV) (\<lambda>x. ennreal (spmf a x))) +
    (\<integral>\<^sup>+ y. ennreal (spmf (d y) x) \<partial>density (count_space UNIV) (\<lambda>x. ennreal (spmf b x)))"
    unfolding ennreal_spmf_bind spmf_density by rule
  also have "\<dots> = 
     (\<Sum>\<^sup>+ y. ennreal (spmf a y) * ennreal (spmf (d y) x)) +
     (\<Sum>\<^sup>+ y. ennreal (spmf b y) * ennreal (spmf (d y) x))"
    apply (subst nn_integral_density) apply auto[2]
    apply (subst nn_integral_density) by auto
  also have "\<dots> = (\<Sum>\<^sup>+ y. ennreal (spmf c y) * ennreal (spmf (d y) x))"
    using assms[unfolded spmf_sums_def, rule_format, symmetric]
    by (auto simp: nn_integral_add Groups.mult_ac(2) nat_distrib(2))
  also have "\<dots> = 
    (\<integral>\<^sup>+ y. ennreal (spmf (d y) x) \<partial>density (count_space UNIV) (\<lambda>x. ennreal (spmf c x)))"
    apply (subst nn_integral_density) by auto
  also have "\<dots>
    = (\<integral>\<^sup>+ y. ennreal (spmf (d y) x) \<partial>measure_spmf c)"
    unfolding ennreal_spmf_bind spmf_density by rule
  also have "\<dots> = ennreal (spmf (c \<bind> d) x)"
    by (auto simp: ennreal_spmf_bind)
  finally show "spmf (a \<bind> d) x + spmf (b \<bind> d) x = spmf (c \<bind> d) x"
    by (smt ennreal_inj ennreal_plus pmf_nonneg)
qed

lemma spmf_sums_bind2:
  fixes a b c :: "'a \<Rightarrow> 'b spmf" and d :: "'a spmf"
  assumes "\<And>x. x\<in>set_spmf d \<Longrightarrow> spmf_sums (a x) (b x) (c x)"
  shows "spmf_sums (d \<bind> a) (d \<bind> b) (d \<bind> c)"
proof (rule spmf_sumsI)
  fix x
  have "ennreal (spmf (d \<bind> a) x) + ennreal (spmf (d \<bind> b) x)
    = (\<integral>\<^sup>+ y. ennreal (spmf (a y) x) \<partial>measure_spmf d) +
      (\<integral>\<^sup>+ y. ennreal (spmf (b y) x) \<partial>measure_spmf d)"
    by (auto simp: ennreal_spmf_bind)
  also have "\<dots> = (\<integral>\<^sup>+ y. ennreal (spmf (a y) x + spmf (b y) x) \<partial>measure_spmf d)"
    apply (subst nn_integral_add[symmetric]) by auto
  also have "\<dots> = (\<integral>\<^sup>+ y. ennreal (spmf (c y) x) \<partial>measure_spmf d)"
    apply (rule nn_integral_cong_AE)
    using assms apply (auto simp: spmf_sums_def)
    by (simp add: ennreal_plus_if)
  also have "\<dots> = ennreal (spmf (d \<bind> c) x)"
    by (auto simp: ennreal_spmf_bind)
  finally show "spmf (d \<bind> a) x + spmf (d \<bind> b) x = spmf (d \<bind> c) x"
    by (smt ennreal_inj ennreal_plus pmf_nonneg)
qed

lemma spmf_sums_If:
  "spmf_sums 
  (semantics (Assert e # P) m)
  (semantics (Assert (\<lambda>m. \<not> e m) # Q) m)
  (semantics1 (IfThenElse e P Q) m)"
  apply (rule spmf_sumsI) by auto

lemma spmf_sums_If':
  fixes m :: 'mem
  shows "spmf_sums
  (semantics (P1 @ Assert e # T @ P2) m)
  (semantics (P1 @ Assert (\<lambda>m. \<not> e m) # F @ P2) m)
  (semantics (P1 @ (IfThenElse e T F) # P2) m)"
proof -
  have sem1: "semantics [i] = semantics1 i" for i::"'mem instruction" by auto
  have "spmf_sums
          (semantics (P1 @ (Assert e # T) @ P2) m)
          (semantics (P1 @ (Assert (\<lambda>m. \<not> e m) # F) @ P2) m)
          (semantics (P1 @ [IfThenElse e T F] @ P2) m)"
    unfolding semantics_seq
    apply (rule spmf_sums_bind2)
    apply (rule spmf_sums_bind1)
    unfolding sem1
    by (rule spmf_sums_If)
  then show ?thesis by auto
qed

lemma spmf_sums_hoare:
  assumes "hoare A a B"
  assumes "hoare A b B"
  assumes "\<And>m. A m \<Longrightarrow> spmf_sums (semantics a m) (semantics b m) (semantics c m)"
  shows "hoare A c B"
proof (rule hoareI)
  fix m assume "A m"
  then have sums: "spmf_sums (semantics a m) (semantics b m) (semantics c m)"
    using assms by simp
  show "pred_spmf B (semantics c m)"
  proof (unfold pred_spmf_def, rule ballI, rename_tac m')
    fix m' assume "m' \<in> set_spmf (semantics c m)"
    then have "spmf (semantics c m) m' > 0"
      by (simp add: spmf_eq_0_set_spmf)
    moreover from sums have "spmf (semantics a m) m' + spmf (semantics b m) m' = spmf (semantics c m) m'"
      unfolding spmf_sums_def by auto
    ultimately have ab: "spmf (semantics a m) m' > 0 \<or> spmf (semantics b m) m' > 0"
      by auto
    have B: "B m'" if "spmf (semantics p m) m' > 0" and "hoare A p B" for p
    proof -
      from that(1) have "m' \<in> set_spmf (semantics p m)"
        using spmf_eq_0_set_spmf by force
      with \<open>A m\<close> and \<open>hoare A p B\<close> show ?thesis
        unfolding hoare_def pred_spmf_def by auto
    qed
    with ab assms show "B m'"
      by auto
  qed
qed

lemma if_merge_hoare:
  assumes "hoare A (P1 @ Assert e # T @ P2) B"
  assumes "hoare A (P1 @ Assert (\<lambda>m. \<not> e m) # F @ P2) B"
  shows "hoare A (P1 @ (IfThenElse e T F) # P2) B"
  using assms apply (rule spmf_sums_hoare)
  by (rule spmf_sums_If')



subsection \<open>Concrete syntax for programs\<close>

syntax "_expression_prhl" :: "'a \<Rightarrow> 'a" ("EXPR[_]")
syntax "_expression2_prhl" :: "'a \<Rightarrow> 'a" ("EXPR2[_]")
syntax "_invariant_prhl" :: "'a \<Rightarrow> 'a" ("INV[_]")
syntax "_invariant2_prhl" :: "'a \<Rightarrow> 'a" ("INV2[_]")
hide_type (open) id
syntax "_variable_prhl" :: "id \<Rightarrow> 'a" ("$_" 1000)
syntax "_the_memory_prhl" :: "id \<Rightarrow> 'a" ("$\<MM>" 1000)
syntax "_the_memory1_prhl" :: "id \<Rightarrow> 'a" ("$\<MM>1" 1000)
syntax "_the_memory2_prhl" :: "id \<Rightarrow> 'a" ("$\<MM>2" 1000)

ML_file \<open>prhl.ML\<close>

parse_translation \<open>let 
fun EXPR_like T ctxt [e] = PRHL.tr_EXPR_like T ctxt e
fun EXPR2_like T ctxt [e] = PRHL.tr_EXPR2_like T ctxt e
in
[
  (\<^syntax_const>\<open>_expression_prhl\<close>, EXPR_like dummyT),
  (\<^syntax_const>\<open>_expression2_prhl\<close>, EXPR2_like dummyT),
  (\<^syntax_const>\<open>_invariant_prhl\<close>, EXPR_like HOLogic.boolT),
  (\<^syntax_const>\<open>_invariant2_prhl\<close>, EXPR2_like HOLogic.boolT)
] end\<close>

abbreviation skip ("PROG[]") where "skip \<equiv> ([]::'mem program)"

nonterminal instruction_syntax_prhl and program_syntax_prhl and block_syntax_prhl

syntax "_instruction_set_prhl" :: "id \<Rightarrow> 'a \<Rightarrow> instruction_syntax_prhl" ("_ := _")
syntax "_instruction_sample_prhl" :: "id \<Rightarrow> 'a \<Rightarrow> instruction_syntax_prhl" ("_ <$ _")
syntax "_instruction_assert_prhl" :: "'a \<Rightarrow> instruction_syntax_prhl" ("assert _")
syntax "_instruction_if_prhl" 
  :: "'a \<Rightarrow> block_syntax_prhl \<Rightarrow> block_syntax_prhl \<Rightarrow> instruction_syntax_prhl"
            ("if _ then _ else _")
syntax "_instruction_prhl" :: "instruction_syntax_prhl \<Rightarrow> 'a" ("INSTR[_]")

syntax "_block_prhl" :: "program_syntax_prhl \<Rightarrow> block_syntax_prhl" ("{_}")
syntax "_singleton_block_prhl" :: "instruction_syntax_prhl \<Rightarrow> block_syntax_prhl" ("_")
syntax "_empty_block_prhl" :: "block_syntax_prhl" ("{}")
syntax "_print_as_block_prhl" :: "_ \<Rightarrow> _"

syntax "_program_cons_prhl" :: "instruction_syntax_prhl \<Rightarrow> program_syntax_prhl \<Rightarrow> program_syntax_prhl" ("_; _")
syntax "_program_single_prhl" :: "instruction_syntax_prhl \<Rightarrow> program_syntax_prhl" ("_")
syntax "_program_prhl" :: "program_syntax_prhl \<Rightarrow> 'a" ("PROG[_]")

translations "_instruction_prhl (_instruction_set_prhl x e)"
          \<rightharpoonup> "CONST Set x (_expression_prhl e)"
translations "_instruction_prhl (_instruction_sample_prhl x e)" 
          \<rightharpoonup> "CONST Sample x (_expression_prhl e)"
translations "_instruction_prhl (_instruction_assert_prhl e)"
          \<rightharpoonup> "CONST Assert (_expression_prhl e)"
translations "_instruction_prhl (_instruction_if_prhl c P Q)"
          \<rightharpoonup> "CONST IfThenElse (_expression_prhl c) P Q"

translations "_block_prhl b" \<rightharpoonup> "_program_prhl b"
translations "_singleton_block_prhl c" \<rightharpoonup> "[_instruction_prhl c]"
translations "_empty_block_prhl" \<rightharpoonup> "CONST Nil"
translations "_block_prhl p" \<leftharpoondown> "_print_as_block_prhl (_program_prhl p)"
translations "_empty_block_prhl" \<leftharpoondown> "_print_as_block_prhl []"
translations "i" \<leftharpoondown> "_block_prhl (_program_single_prhl i)"

translations "_program_prhl (_program_cons_prhl i is)" \<rightleftharpoons> "_instruction_prhl i # _program_prhl is"
translations "_program_prhl (_program_single_prhl i)" \<rightleftharpoons> "_instruction_prhl i # CONST skip"
translations "_program_prhl (_program_single_prhl i)" \<rightleftharpoons> "[_instruction_prhl i]"

(* Print translations *)

print_translation \<open>[
(\<^const_syntax>\<open>Set\<close>, fn ctxt => fn [x,e] =>
  Const(\<^syntax_const>\<open>_instruction_prhl\<close>,dummyT) $
    (Const(\<^syntax_const>\<open>_instruction_set_prhl\<close>,dummyT) $ x $ PRHL.print_tr_EXPR_like ctxt e)),

(\<^const_syntax>\<open>Sample\<close>, fn ctxt => fn [x,e] =>
  Const(\<^syntax_const>\<open>_instruction_prhl\<close>,dummyT) $
    (Const(\<^syntax_const>\<open>_instruction_sample_prhl\<close>,dummyT) $ x $ PRHL.print_tr_EXPR_like ctxt e)),

(\<^const_syntax>\<open>Assert\<close>, fn ctxt => fn [e] =>
  Const(\<^syntax_const>\<open>_instruction_prhl\<close>,dummyT) $
    (Const(\<^syntax_const>\<open>_instruction_assert_prhl\<close>,dummyT) $ PRHL.print_tr_EXPR_like ctxt e)),

(\<^const_syntax>\<open>IfThenElse\<close>, fn ctxt => fn [c,p,q] =>
  Const(\<^syntax_const>\<open>_instruction_prhl\<close>,dummyT) $
    ((Const(\<^syntax_const>\<open>_instruction_if_prhl\<close>,dummyT) $
      PRHL.print_tr_EXPR_like ctxt c) $ 
      (Const(\<^syntax_const>\<open>_print_as_block_prhl\<close>,dummyT)$p) $
      (Const(\<^syntax_const>\<open>_print_as_block_prhl\<close>,dummyT)$q)))

]\<close>

term \<open>INSTR[x <$ return_spmf ($x+$y)]\<close>

term \<open>INSTR[assert $x=1]\<close>

term \<open>[Set x (\<lambda>mem. \<lambda>x. x mem)]\<close>

term \<open>INSTR[x := eval_var x $\<MM>]\<close>

term \<open>INSTR[x := $x]\<close>

term \<open>\<lambda>z. PROG[x := z]\<close>

term \<open>PROG[x := 0; if $x=$y then {y := 0; y := 1} else x := 1]\<close>

term \<open>PROG[]\<close>

term "Nil :: 'a instruction list"

end

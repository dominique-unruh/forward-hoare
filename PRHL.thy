theory PRHL
  imports CryptHOL.CryptHOL Forward_Hoare
begin

no_notation m_inv ("inv\<index> _" [81] 80)

section \<open>Programs\<close>

definition "less_eq_card A B \<longleftrightarrow> (\<exists>f. inj_on f A \<and> range f \<subseteq> B)"

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

type_synonym ('mem,'val) raw_var = \<open>('mem\<Rightarrow>'val) * ('val\<Rightarrow>'mem\<Rightarrow>'mem)\<close>
type_synonym 'mem raw_untyped_var = \<open>'mem set * ('mem,'mem) raw_var\<close>

definition \<open>valid_raw_var = (\<lambda>(R,g::'mem\<Rightarrow>'val,s::'val\<Rightarrow>'mem\<Rightarrow>'mem). 
  (\<forall>m. \<forall>a\<in>R. g (s a m) = a) \<and> (\<forall>m. s (g m) m = m)
    \<and> (\<forall>m. \<forall>a\<in>R. \<forall>b\<in>R. s a (s b m) = s a m) \<and> range g = R)\<close>

lemma valid_raw_varI:
  fixes R and g and s
  assumes "\<And>m a. a\<in>R \<Longrightarrow> g (s a m) = a"
  assumes "\<And>m. s (g m) m = m"
  assumes "\<And>m a b. a\<in>R \<Longrightarrow> b\<in>R \<Longrightarrow> s a (s b m) = s a m"
  assumes "range g \<subseteq> R"
  shows "valid_raw_var (R,g,s)"
  unfolding valid_raw_var_def using assms apply auto
  by (metis (full_types) rangeI) 

lemma valid_raw_var_setget: "valid_raw_var (R,g,s) \<Longrightarrow> a\<in>R \<Longrightarrow> g (s a m) = a"
  and valid_raw_var_getset: "valid_raw_var (R,g,s) \<Longrightarrow> s (g m) m = m"
  and valid_raw_var_setset: "valid_raw_var (R,g,s) \<Longrightarrow> a\<in>R \<Longrightarrow> b\<in>R \<Longrightarrow> s a (s b m) = s a m"
  and valid_raw_var_rangeget: "valid_raw_var (R,g,s) \<Longrightarrow> range g = R"
  unfolding valid_raw_var_def by auto

(* definition "has_variables (_::'mem itself) (_::'val itself) \<longleftrightarrow> 
  (\<exists>v::('mem,'val) raw_var. valid_raw_var (UNIV,v))" *)

(* lemma has_variablesI[intro]: "valid_raw_var (f::'mem\<Rightarrow>'val\<times>'mem, UNIV) \<Longrightarrow> has_variables TYPE('mem) TYPE('val)" *)
  (* unfolding has_variables_def by auto *)

definition raw_dummy_var :: "('mem,'val) raw_var" where
  "raw_dummy_var = ((\<lambda>_. undefined), (\<lambda>_. id))"

typedef ('mem,'val) var = "{v::('mem,'val) raw_var. valid_raw_var (UNIV,v) \<or> v = raw_dummy_var}"
  apply auto by (metis prod.exhaust) 
setup_lifting type_definition_var


definition "some_embedding = (if less_eq_card (UNIV::'a set) (UNIV::'b set) then
(SOME i::'a\<Rightarrow>'b. inj i \<and> i undefined = undefined) else (\<lambda>_. undefined))"

lemma raw_dummy_var_valid: "valid_raw_var ({undefined},raw_dummy_var)"
  unfolding valid_raw_var_def raw_dummy_var_def by auto

typedef 'mem untyped_var = 
  "Collect valid_raw_var :: ('mem set \<times> ('mem,'mem) raw_var) set"
  apply (rule exI[of _ "({undefined},raw_dummy_var)"])
  by (simp add: raw_dummy_var_valid)
setup_lifting type_definition_untyped_var

lemma 
  shows some_embedding_inj: "less_eq_card (UNIV::'a set) (UNIV::'b set) \<Longrightarrow> inj (some_embedding::'a\<Rightarrow>'b)" 
    and some_embedding_undefined[simp]: "(some_embedding::'a\<Rightarrow>'b) undefined = undefined"
proof -
  let ?i = "some_embedding::'a\<Rightarrow>'b"
  let ?less = "less_eq_card (UNIV::'a set) (UNIV::'b set)"
  have props: "inj ?i \<and> ?i undefined = undefined" if "?less"
  proof -
    from that obtain i::"'a \<Rightarrow> 'b" where "inj i"
      unfolding less_eq_card_def by auto
    define j where "j = Fun.swap undefined (i undefined) id \<circ> i"
    have 1: "inj j"
      by (simp add: \<open>inj i\<close> j_def inj_compose)
    have 2: "j undefined = undefined"
      unfolding j_def by auto
    show ?thesis
      unfolding some_embedding_def apply (simp add: that)
      apply (rule someI_ex[of "\<lambda>i. inj i \<and> i undefined = undefined"])
      using 1 2 by auto
  qed
  then show "?less \<Longrightarrow> inj ?i" by simp

  have "?i undefined = undefined" if "\<not> ?less"
    using that unfolding some_embedding_def by simp
  with props
  show "?i undefined = undefined"
    by auto
qed

lemma some_embedding_unit[simp]: "some_embedding () = undefined"
  unfolding unit_eq[of undefined, symmetric] 
  by (rule some_embedding_undefined)

lemma valid_raw_var_less_eq_card:
  fixes R :: \<open>'val set\<close> and v :: "('mem,'val) raw_var"
  assumes "valid_raw_var (R,v)"
  shows "less_eq_card R (UNIV::'mem set)"
proof -
  fix m
  obtain g s where v_def: "v = (g,s)" 
    apply atomize_elim by auto
  define f where "f a = s a m" for a
  have \<open>inj_on f R\<close>
    apply (rule inj_on_inverseI[where f=f and g=g])
    unfolding f_def apply (rule valid_raw_var_setget[of _ g s])
    using assms unfolding v_def by auto
  then show ?thesis
    unfolding less_eq_card_def by auto
qed

lemma bij_betw_map_prod:
  assumes "bij_betw f A B" and "bij_betw g C D"
  shows "bij_betw (map_prod f g) (A \<times> C) (B \<times> D)"
  apply (rule bij_betw_byWitness[where f'="map_prod (inv_into A f) (inv_into C g)"])
  using assms
  by (auto simp add: bij_betw_inv_into_left bij_betw_inv_into_right bij_betw_apply 
                     bij_betw_imp_surj_on inv_into_into)

definition mk_var_untyped_raw :: \<open>('mem,'val) raw_var \<Rightarrow> 'mem raw_untyped_var\<close> where
  "mk_var_untyped_raw = (\<lambda>(g,s).
      if valid_raw_var (UNIV,g,s) then
      (range (some_embedding::'val\<Rightarrow>'mem),
       some_embedding o g,
       s o inv some_embedding)
      else ({undefined},raw_dummy_var))"

lemma mk_var_untyped_raw_valid: 
  fixes v :: "('mem,'val) raw_var"
  shows "valid_raw_var (mk_var_untyped_raw v)"
proof (cases \<open>valid_raw_var (UNIV, v)\<close>)
  case False
  then show ?thesis
    unfolding mk_var_untyped_raw_def
    using raw_dummy_var_valid by (auto simp: case_prod_beta)
next
  case True
  obtain g s where v_def: "v = (g,s)"
    apply atomize_elim by auto
  define i where "i = (some_embedding::'val\<Rightarrow>'mem)"
  from True have "less_eq_card (UNIV::'val set) (UNIV::'mem set)"
    by (rule valid_raw_var_less_eq_card)
  then have "inj i"
    unfolding i_def
    by (rule some_embedding_inj)

  from True have raw_v: "mk_var_untyped_raw v = (range i, i \<circ> g, s \<circ> inv i)"
    unfolding mk_var_untyped_raw_def v_def i_def by simp
  have setget: "(i \<circ> g) ((s \<circ> inv i) a m) = a" (is "?lhs = _") if "a \<in> range i" for a m
  proof -
    from that obtain b where a_def: "a = i b"
      by auto
    then have "?lhs = i (g (s (inv i (i b)) m))"
      unfolding o_def by simp
    also have "\<dots> = i (g (s b m))"
      apply (subst inv_f_f) using \<open>inj i\<close> by simp_all
    also from True have "\<dots> = i b"
      apply (subst valid_raw_var_setget[of UNIV g s])
      using True unfolding v_def by auto
    also have "\<dots> = a"
      unfolding a_def by simp
    finally show ?thesis
      by -
  qed
  have getset: "(s \<circ> inv i) ((i \<circ> g) m) m = m" for m
    unfolding o_def inv_f_f[OF \<open>inj i\<close>]
    using True unfolding v_def by (rule valid_raw_var_getset)
  have setset: \<open>(s \<circ> inv i) a ((s \<circ> inv i) b m) = (s \<circ> inv i) a m\<close> for m a b
    unfolding o_def using True unfolding v_def 
    apply (rule valid_raw_var_setset[of _ g s])
    by auto
  have rangeg: "range (i \<circ> g) \<subseteq> range i"
    by auto
  show ?thesis
    unfolding raw_v
    using setget getset setset rangeg by (rule valid_raw_varI)
qed

lift_definition mk_var_untyped :: "('mem,'val) var \<Rightarrow> 'mem untyped_var" is mk_var_untyped_raw
  by (simp add: mk_var_untyped_raw_valid)

lift_definition valid_var :: "('mem,'val) var \<Rightarrow> bool" is 
  "\<lambda>v. valid_raw_var (UNIV,v)".

lift_definition dummy_var :: "('mem,'val) var" is raw_dummy_var
  by simp

abbreviation "(unit_var :: ('mem,'a::CARD_1) var) \<equiv> dummy_var"

lemma dummy_var_untyped_raw[simp]: 
  "mk_var_untyped_raw (raw_dummy_var::('mem,'val) raw_var) = ({undefined}, raw_dummy_var)"
proof (cases "valid_raw_var (UNIV, raw_dummy_var :: ('mem,'val) raw_var)")
  case True
  define g s where "g = fst (raw_dummy_var::('mem,'val) raw_var)"
    and "s = snd (raw_dummy_var::('mem,'val) raw_var)"
  have "range g = UNIV"
    apply (rule valid_raw_var_rangeget[of _ g s])
    unfolding g_def s_def using True by auto
  moreover have "range g = {undefined}"
    unfolding g_def raw_dummy_var_def by auto
  ultimately have UNIV_val: "UNIV = {undefined::'val}"
    by simp

  show "mk_var_untyped_raw (raw_dummy_var::('mem,'val) raw_var) = ({undefined}, raw_dummy_var)"
    using raw_dummy_var_valid 
    unfolding mk_var_untyped_raw_def raw_dummy_var_def UNIV_val
    by simp
next
  case False
  show "mk_var_untyped_raw (raw_dummy_var::('mem,'val) raw_var) = ({undefined}, raw_dummy_var)"
    using False
    by (auto simp: mk_var_untyped_raw_def case_prod_beta)
qed

lemma dummy_var_untyped[simp]: 
  "Rep_untyped_var (mk_var_untyped (dummy_var::('mem,'val) var)) = ({undefined},raw_dummy_var)"
  apply transfer by simp

datatype 'mem instruction = 
  SetRaw "'mem untyped_var" "'mem untyped_expression"
  | SampleRaw "'mem untyped_var" "'mem untyped_spmf_expression"

definition Set :: "('mem,'val) var \<Rightarrow> ('mem,'val) expression \<Rightarrow> 'mem instruction" where
  "Set x e = SetRaw (mk_var_untyped x) ((some_embedding::'val\<Rightarrow>'mem) o e)"

definition Sample :: "('mem,'val) var \<Rightarrow> ('mem,'val spmf) expression \<Rightarrow> 'mem instruction" where
  "Sample x e = SampleRaw (mk_var_untyped x) (map_spmf (some_embedding::'val\<Rightarrow>'mem) o e)"

type_synonym 'mem "program" = "'mem instruction list"

lift_definition update_var :: "('mem,'a) var \<Rightarrow> 'a \<Rightarrow> 'mem \<Rightarrow> 'mem" is snd.

lift_definition eval_var :: "('mem,'a) var \<Rightarrow> 'mem \<Rightarrow> 'a" is fst.

lemma invalid_is_dummy_var:
  assumes "\<not> valid_var v"
  shows "v = dummy_var"
  using assms apply transfer by simp

lemma update_dummy_var[simp]: "update_var dummy_var a m = m"
  apply transfer unfolding raw_dummy_var_def by simp

lemma eval_dummy_var[simp]: "eval_var dummy_var m = undefined"
  apply transfer unfolding raw_dummy_var_def by simp

definition "force_into a S = (if a\<in>S then a else (SOME a. a\<in>S))"
lemma force_into_forces:
  "S \<noteq> {} \<Longrightarrow> force_into a S \<in> S"
  by (auto simp: some_in_eq force_into_def)
lemma force_into_id:
  "a \<in> S \<Longrightarrow> force_into a S = a"
  by (auto simp: force_into_def)
lemma force_into_range[simp]:
  "force_into (f a) (range f) = f a"
  by (auto simp: force_into_def)
lemma force_into_singleton[simp]:
  "force_into a {b} = b"
  by (auto simp: force_into_def)

lift_definition update_untyped_var :: "'mem untyped_var \<Rightarrow> 'mem \<Rightarrow> 'mem \<Rightarrow> 'mem" is
  (* "\<lambda>(x,S) a m. if valid_raw_var (x, S) then inv x (force_into a S, snd (x m)) else m". *)
  \<open>\<lambda>(R,g,s) a m. s (force_into a R) m\<close>.

lift_definition eval_untyped_var :: "'mem untyped_var \<Rightarrow> 'mem \<Rightarrow> 'mem" is
  (* \<open>\<lambda>(x,S) m. if valid_raw_var (x, S) then fst (x m) else undefined\<close>. *)
  \<open>\<lambda>(R,g,s) m. g m\<close>.

lemma eval_untyped_var:
  fixes x :: "('mem,'val) var"
  shows "eval_untyped_var (mk_var_untyped x) m
       = (some_embedding::'val\<Rightarrow>'mem) (eval_var x m)"
proof (transfer fixing: m)
  fix x :: "('mem,'val) raw_var"
  obtain g s where x_def: "x = (g,s)" 
    apply atomize_elim by auto
  define i where "i = (some_embedding::'val\<Rightarrow>'mem)"
  assume "valid_raw_var (UNIV, x) \<or> x = raw_dummy_var"
  then show "(case mk_var_untyped_raw x of (R, g, s) \<Rightarrow> g) m = some_embedding (fst x m)"
  proof (cases)
    case left
    then have "mk_var_untyped_raw x = (range i, i \<circ> g, s \<circ> inv i)"
      unfolding x_def mk_var_untyped_raw_def i_def
      by (auto simp: case_prod_beta)
    then show ?thesis
      unfolding x_def i_def by auto
  next
    case right
    show ?thesis
      unfolding right dummy_var_untyped_raw
      by (simp add: raw_dummy_var_def)
  qed
qed

lemma update_untyped_var:
  fixes x :: "('mem,'val) var" and a :: 'val
  shows "update_untyped_var (mk_var_untyped x) ((some_embedding::'val\<Rightarrow>'mem) a) m
       = update_var x a m"
proof (transfer fixing: m a)
  fix x :: "('mem,'val) raw_var"
  obtain g s where x_def: "x = (g,s)" 
    apply atomize_elim by auto
  define i where "i = (some_embedding::'val\<Rightarrow>'mem)"
  assume "valid_raw_var (UNIV, x) \<or> x = raw_dummy_var"
  then show "(case mk_var_untyped_raw x of (R, g, s) \<Rightarrow> \<lambda>a. s (force_into a R))
            (some_embedding a) m = snd x a m"
  proof (cases)
    case left
    then have x_untyped: "mk_var_untyped_raw x = (range i, i \<circ> g, s \<circ> inv i)"
      unfolding x_def mk_var_untyped_raw_def i_def
      by (auto simp: case_prod_beta)
    from left have "less_eq_card (UNIV::'val set) (UNIV::'mem set)"
      by (rule valid_raw_var_less_eq_card)
    then have "inj i"
      unfolding i_def
      by (rule some_embedding_inj)
    then have "inv i (i a) = a"
      by (rule inv_f_f)
    with x_untyped show ?thesis
      unfolding x_def i_def by auto
  next
    case right
    show ?thesis
      unfolding right dummy_var_untyped_raw
      by (simp add: raw_dummy_var_def)
  qed
qed


lemma eval_update_var[simp]:
  fixes m :: 'mem and a :: 'val
  (* assumes "has_variables TYPE('mem) TYPE('a)" *)
  assumes "valid_var x"
  shows \<open>eval_var x (update_var x a m) = a\<close>
  using assms apply transfer unfolding valid_raw_var_def by auto

section \<open>Semantics\<close>

fun semantics1 :: "'mem instruction \<Rightarrow> 'mem \<Rightarrow> 'mem spmf" where
  "semantics1 (SetRaw x e) m = return_spmf (update_untyped_var x (e m) m)"
| "semantics1 (SampleRaw x e) m = map_spmf (\<lambda>a. update_untyped_var x a m) (e m)"

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

fun semantics :: "'mem program \<Rightarrow> 'mem \<Rightarrow> 'mem spmf" where
  "semantics [] m = return_spmf m"
| "semantics (c#p) m = bind_spmf (semantics1 c m) (semantics p)"

lemma semantics_Nil[simp]: "semantics [] = return_spmf"
  by auto

type_synonym 'mem "invariant" = "'mem \<Rightarrow> bool"
type_synonym ('m1,'m2) "rinvariant" = "'m1 \<Rightarrow> 'm2 \<Rightarrow> bool"

definition "hoare" :: "'mem invariant \<Rightarrow> 'mem program \<Rightarrow> 'mem invariant \<Rightarrow> bool" where
  "hoare A p B \<longleftrightarrow> (\<forall>m. A m \<longrightarrow> pred_spmf B (semantics p m))"

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

definition "independent_of e x \<longleftrightarrow> (\<forall>m a. e m = e (update_var x a m))"
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

definition "instructions_commute a b \<longleftrightarrow> semantics [a,b] = semantics [b,a]"

definition "independent_vars a b \<longleftrightarrow> (\<forall>x y mem.
   update_var b y (update_var a x mem) = update_var a x (update_var b y mem))"

(* TODO: generalize using independent_of_prog or similar? Or add cases for Sample? *)
lemma commute_indep:
  fixes a :: "('mem,'a) var" and b :: "('mem,'b) var"
  assumes "independent_of f a"
  assumes "independent_of e b"
  assumes "independent_vars a b"
  shows "instructions_commute (Set a e) (Set b f)"
proof -
  have \<open>semantics [Set a e, Set b f] mem = semantics [Set b f, Set a e] mem\<close> for mem
  proof -
    have "f (update_var a (e mem) mem) = f mem"
      by (rule assms(1)[unfolded independent_of_def, rule_format, symmetric])
    then have 1: "semantics [Set a e, Set b f] mem
       = return_spmf (update_var b (f mem) (update_var a (e mem) mem))"
      by simp
    have "e (update_var b (f mem) mem) = e mem"
      by (rule assms(2)[unfolded independent_of_def, rule_format, symmetric])
    then have 2: "semantics [Set b f, Set a e] mem
       = return_spmf (update_var a (e mem) (update_var b (f mem) mem))"
      by (simp add: )
    show "semantics [Set a e, Set b f] mem = semantics [Set b f, Set a e] mem"
      unfolding 1 2
      using assms(3) unfolding independent_vars_def by simp
  qed
  then show ?thesis
    unfolding instructions_commute_def by auto
qed

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

ML \<open>
fun infer ctxt ts = 
  Drule.infer_instantiate' ctxt (ts |> map (Thm.cterm_of ctxt #> SOME))
\<close>

named_theorems independence

lemma independent_of_const[simp]:
  shows "independent_of (\<lambda>m. a) x"
  unfolding independent_of_def by simp

lemma independent_of_split[intro]:
  assumes "independent_of a x"
  assumes "independent_of b x"
  shows "independent_of (\<lambda>m. (a m) (b m)) x"
  using assms unfolding independent_of_def by auto

lemma update_var_current:
  fixes x :: \<open>('mem,'x) var\<close>
  shows "update_var x (eval_var x m) m = m"
proof (cases "valid_var x")
  case True
  then show ?thesis
    apply (transfer fixing: m)
    unfolding valid_raw_var_def by auto
next
  case False
  show ?thesis
    unfolding invalid_is_dummy_var[OF False]
    by simp
qed

lemma update_var_twice: 
  fixes x :: \<open>('mem,'x) var\<close>
  shows "update_var x a (update_var x b m) = update_var x a m"
proof (cases "valid_var x")
  case True
  then show ?thesis
    apply (transfer fixing: m)
    unfolding valid_raw_var_def by auto
next
  case False
  show ?thesis
    unfolding invalid_is_dummy_var[OF False]
    by simp
qed

lemma independent_of_var[intro]:
  fixes x :: "('mem,'x) var" and y :: "('mem,'y) var"
  assumes "independent_vars x y"
  shows "independent_of (\<lambda>m. eval_var x m) y"
  unfolding independent_of_def independent_vars_def
proof (rule+, cases "valid_var x")
  case True
  fix m a
  have "eval_var x m = eval_var x (update_var x (eval_var x m) (update_var y a m))"
    using True by (rule eval_update_var[symmetric])
  also have "\<dots> = eval_var x (update_var y a (update_var x (eval_var x m) m))"
    using assms unfolding independent_vars_def by simp
  also have "\<dots> = eval_var x (update_var y a m)"
    by (subst update_var_current, simp)
  finally show "eval_var x m = eval_var x (update_var y a m)"
    by -
next
  case False
  fix m a
  show "eval_var x m = eval_var x (update_var y a m)"
    unfolding invalid_is_dummy_var[OF False] by simp
qed

lemma sort_program_empty_aux:
  "semantics [] = semantics []"
  by simp

lemma sort_program_aux:
  assumes "semantics p = semantics q"
  assumes "semantics (i#q) = semantics r"
  shows "semantics (i#p) = semantics r"
  using assms by (simp add: semantics.simps[abs_def] o_def)

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

lemma wp_generic[hoare_wp add]:
  fixes x :: "('mem,'val) var"
  assumes "invariant \<equiv> postcondition_default2 p1 p2 A"
  assumes "\<And>m1 m2. A m1 m2 \<Longrightarrow> A' m1 m2"
  assumes "\<lbrakk>SOLVER wp_tac\<rbrakk> \<forall>m1 m2. postcondition_default2 p1 p2 A' m1 m2 \<longrightarrow> B m1 m2"
  shows "\<forall>m1 m2. invariant m1 m2 \<longrightarrow> B m1 m2"
  using assms(2,3) unfolding assms(1) postcondition_default2_def 
  apply auto by metis

lemma wp_generic1[hoare_wp add]:
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

lemma wp_Set_cons1:
  assumes "\<lbrakk>SOLVER wp_tac\<rbrakk> \<forall>mem1 mem2. postcondition_default2 p1 p2 M mem1 mem2 \<longrightarrow> B mem1 mem2"
  shows "\<forall>mem1 mem2. postcondition_default2 (Set x e # p1) p2 (\<lambda>m1 m2. M (update_var x (e m1) m1) m2) mem1 mem2 \<longrightarrow> B mem1 mem2"
  using assms unfolding postcondition_default2_def
  by auto

lemma wp_Sample_cons1:
  assumes "\<lbrakk>SOLVER wp_tac\<rbrakk> \<forall>mem1 mem2. postcondition_default2 p1 p2 M mem1 mem2 \<longrightarrow> B mem1 mem2"
  shows "\<forall>mem1 mem2. postcondition_default2 (Sample x e # p1) p2
               (\<lambda>m1 m2. \<forall>a\<in>set_spmf (e m1). M (update_var x a m1) m2) mem1 mem2 \<longrightarrow> B mem1 mem2"
  using assms unfolding postcondition_default2_def apply auto by blast

lemma wp_Set_cons2:
  assumes "\<lbrakk>SOLVER wp_tac\<rbrakk> \<forall>mem1 mem2. postcondition_default2 p1 p2 M mem1 mem2 \<longrightarrow> B mem1 mem2"
  shows "\<forall>mem1 mem2. postcondition_default2 p1 (Set x e # p2) (\<lambda>m1 m2. M m1 (update_var x (e m2) m2)) mem1 mem2 \<longrightarrow> B mem1 mem2"
  using assms unfolding postcondition_default2_def
  by auto

lemma wp_Sample_cons2:
  assumes "\<lbrakk>SOLVER wp_tac\<rbrakk> \<forall>mem1 mem2. postcondition_default2 p1 p2 M mem1 mem2 \<longrightarrow> B mem1 mem2"
  shows "\<forall>mem1 mem2. postcondition_default2 p1 (Sample x e # p2) 
               (\<lambda>m1 m2. \<forall>a\<in>set_spmf (e m2). M m1 (update_var x a m2)) mem1 mem2 \<longrightarrow> B mem1 mem2"
  using assms unfolding postcondition_default2_def apply auto by blast

lemma wp_skip12:
  shows "\<forall>mem1 mem2. postcondition_default2 [] [] B mem1 mem2 \<longrightarrow> B mem1 mem2"
  unfolding postcondition_default2_def
  by auto

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

subsection \<open>Concrete syntax for programs\<close>

syntax "_expression_prhl" :: "'a \<Rightarrow> 'a" ("EXPR[_]")
syntax "_expression2_prhl" :: "'a \<Rightarrow> 'a" ("EXPR2[_]")
syntax "_invariant_prhl" :: "'a \<Rightarrow> 'a" ("INV[_]")
syntax "_invariant2_prhl" :: "'a \<Rightarrow> 'a" ("INV2[_]")
hide_type (open) id
syntax "_variable_prhl" :: "id \<Rightarrow> 'a" ("$_" 1000)

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

(* term "(INV2[$x1 = $x2], INV[$x = (1::nat)])" *)

nonterminal instruction_syntax_prhl
syntax "_instruction_set_prhl" :: "id \<Rightarrow> 'a \<Rightarrow> instruction_syntax_prhl" ("_ := _")
syntax "_instruction_sample_prhl" :: "id \<Rightarrow> 'a \<Rightarrow> instruction_syntax_prhl" ("_ <$ _")
syntax "_instruction_prhl" :: "instruction_syntax_prhl \<Rightarrow> 'a" ("INSTR[_]")

translations "_instruction_prhl (_instruction_set_prhl x e)" 
          \<rightharpoonup> "CONST Set x (_expression_prhl e)"
translations "_instruction_prhl (_instruction_sample_prhl x e)" 
          \<rightharpoonup> "CONST Sample x (_expression_prhl e)"

print_translation \<open>[
(\<^const_syntax>\<open>Set\<close>, fn ctxt => fn [x,n] =>
  Const(\<^syntax_const>\<open>_instruction_prhl\<close>,dummyT) $
    (Const(\<^syntax_const>\<open>_instruction_set_prhl\<close>,dummyT) $ x $ n)
  handle TERM("dest_literal_syntax",_) => raise Match),

(\<^const_syntax>\<open>Sample\<close>, fn ctxt => fn [x,n] =>
  Const(\<^syntax_const>\<open>_instruction_prhl\<close>,dummyT) $
    (Const(\<^syntax_const>\<open>_instruction_sample_prhl\<close>,dummyT) $ x $ n)
  handle TERM("dest_literal_syntax",_) => raise Match)
]\<close>

term \<open>INSTR[x <$ return_spmf ($x+$y)]\<close>

nonterminal "program_syntax_prhl"
syntax "_program_cons_prhl" :: "instruction_syntax_prhl \<Rightarrow> program_syntax_prhl \<Rightarrow> program_syntax_prhl" ("_; _")
syntax "_program_single_prhl" :: "instruction_syntax_prhl \<Rightarrow> program_syntax_prhl" ("_")
syntax "_program_prhl" :: "program_syntax_prhl \<Rightarrow> 'a" ("PROG[_]")

translations "_program_prhl (_program_cons_prhl i is)" \<rightleftharpoons> "_instruction_prhl i # _program_prhl is"
translations "_program_prhl (_program_single_prhl i)" \<rightleftharpoons> "[_instruction_prhl i]"

term \<open>PROG[x := 0; x := $x+1]\<close>

end

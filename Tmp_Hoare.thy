theory Tmp_Hoare
  imports Main 
  CryptHOL.CryptHOL
  Forward_Hoare
begin

no_notation m_inv ("inv\<index> _" [81] 80)

section \<open>Programs\<close>

definition "less_eq_card A B \<longleftrightarrow> (\<exists>f. inj_on f A \<and> range f \<subseteq> B)"

lemma less_eq_card[trans]: 
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

definition \<open>valid_var = (\<lambda>(f,S). \<exists>R. bij_betw f UNIV (S \<times> R))\<close> 
definition "has_variables (_::'mem itself) (_::'val itself) \<longleftrightarrow> (\<exists>f::'mem\<Rightarrow>'val\<times>'mem. valid_var (f, UNIV))"

lemma has_variablesI[intro]: "valid_var (f::'mem\<Rightarrow>'val\<times>'mem, UNIV) \<Longrightarrow> has_variables TYPE('mem) TYPE('val)"
  unfolding has_variables_def by auto

typedef ('mem,'val) var = "{f::'mem \<Rightarrow> 'val \<times> 'mem. has_variables TYPE('mem) TYPE('val) \<longrightarrow> valid_var (f, UNIV)}"
  unfolding has_variables_def by auto
setup_lifting type_definition_var


definition "some_embedding = (if less_eq_card (UNIV::'a set) (UNIV::'b set) then
(SOME i::'a\<Rightarrow>'b. inj i \<and> i undefined = undefined) else (\<lambda>_. undefined))"

definition "dummy_untyped_var = (\<lambda>x::'mem. (undefined::'mem,x), {undefined::'mem})"
lemma dummy_untyped_var_valid: "valid_var dummy_untyped_var"
  unfolding valid_var_def dummy_untyped_var_def apply auto
  apply (rule exI[of _ UNIV]) 
  apply (rule bij_betw_byWitness[of _ snd]) by auto

typedef 'mem untyped_var = 
  "Collect valid_var :: (('mem\<Rightarrow>'mem\<times>'mem)\<times>'mem set) set"
  by (rule exI[of _ dummy_untyped_var], simp add: dummy_untyped_var_valid)
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

lemma valid_var_less_eq_card:
  assumes "valid_var (f::'a\<Rightarrow>'b\<times>'a, S)"
  shows "less_eq_card S (UNIV::'a set)"
proof -
  from assms obtain R where bij: \<open>bij_betw f UNIV (S \<times> R)\<close>
    unfolding valid_var_def by auto
  then have \<open>R \<noteq> {}\<close>
    using bij_betw_empty2 by force
  then obtain r where "r \<in> R"
    by auto
  from bij have inj: \<open>inj_on (inv f) (S \<times> R)\<close>
    using bij_betw_imp_inj_on bij_betw_inv_into by blast
  define g where "g = inv f \<circ> (\<lambda>s. (s,r))"
  have \<open>inj_on g S\<close>
    unfolding g_def apply (rule comp_inj_on)
     apply (meson Pair_inject inj_onI)
    using \<open>r \<in> R\<close> inj
    by (metis (no_types, lifting) SigmaI bij bij_betw_imp_surj_on image_subset_iff inj_on_inv_into)
  then show ?thesis
    unfolding less_eq_card_def 
    apply (rule_tac exI[of _ g])
    by auto
qed

lemma bij_betw_map_prod:
  assumes "bij_betw f A B" and "bij_betw g C D"
  shows "bij_betw (map_prod f g) (A \<times> C) (B \<times> D)"
  apply (rule bij_betw_byWitness[where f'="map_prod (inv_into A f) (inv_into C g)"])
  using assms
  by (auto simp add: bij_betw_inv_into_left bij_betw_inv_into_right bij_betw_apply 
                     bij_betw_imp_surj_on inv_into_into)

definition "mk_var_untyped_raw (f::'mem\<Rightarrow>'val \<times> 'mem) =
      (if valid_var (f, UNIV) then
      (map_prod (some_embedding::'val\<Rightarrow>'mem) id \<circ> f,
       range (some_embedding::'val\<Rightarrow>'mem))
      else dummy_untyped_var)"

lemma mk_var_untyped_raw_valid: 
  fixes f :: "'mem \<Rightarrow> 'val \<times> 'mem"
  shows "valid_var (mk_var_untyped_raw f)"
proof (cases \<open>valid_var (f, UNIV)\<close>)
  case False
  then show ?thesis
    unfolding mk_var_untyped_raw_def
    using dummy_untyped_var_valid by auto
next
  case True
  define i where "i = (some_embedding::'val\<Rightarrow>'mem)"
  from True have "less_eq_card (UNIV::'val set) (UNIV::'mem set)"
    by (rule valid_var_less_eq_card)
  then have "inj i"
    unfolding i_def
    by (rule some_embedding_inj)
  from True obtain R where bij_f: "bij_betw f UNIV (UNIV \<times> R)"
    unfolding valid_var_def by auto
  have bij_i: "bij_betw (map_prod i id) (UNIV \<times> R) (range i \<times> R)"
    apply (rule bij_betw_map_prod)
    using \<open>inj i\<close> inj_on_imp_bij_betw apply blast
    by simp
  from bij_f bij_i have "bij_betw (map_prod i id \<circ> f) UNIV (range i \<times> R)"
    using bij_betw_trans by blast
  then have \<open>valid_var (map_prod i id \<circ> f, range i)\<close>
    unfolding valid_var_def by auto
  with True show ?thesis
    by (simp add: i_def mk_var_untyped_raw_def)
qed

lift_definition mk_var_untyped :: "('mem,'val) var \<Rightarrow> 'mem untyped_var" is mk_var_untyped_raw
  by (simp add: mk_var_untyped_raw_valid)

lift_definition unit_var :: "('mem,unit) var" is "\<lambda>m. ((),m)"
  unfolding valid_var_def case_prod_beta apply (rule exI[of _ UNIV])
  apply auto
  by (metis (mono_tags, hide_lams) bijI' old.unit.exhaust snd_conv surj_pair)

lemma unit_var_untyped: "Rep_untyped_var (mk_var_untyped unit_var) = dummy_untyped_var"
proof -
  have valid: "valid_var (Pair (), UNIV)"
    unfolding valid_var_def case_prod_beta apply (rule exI[of _ UNIV])
    apply auto
    by (metis (mono_tags, hide_lams) bijI' old.unit.exhaust snd_conv surj_pair top_unit_def unit_var.rep_eq)
  show ?thesis
    apply transfer
    apply (simp add: valid dummy_untyped_var_def mk_var_untyped_raw_def)
    unfolding dummy_untyped_var_def by auto
qed

datatype 'mem instruction = 
  SetRaw "'mem untyped_var" "'mem untyped_expression"
  | SampleRaw "'mem untyped_var" "'mem untyped_spmf_expression"

definition Set :: "('mem,'val) var \<Rightarrow> ('mem,'val) expression \<Rightarrow> 'mem instruction" where
  "Set x e = SetRaw (mk_var_untyped x) ((some_embedding::'val\<Rightarrow>'mem) o e)"

definition Sample :: "('mem,'val) var \<Rightarrow> ('mem,'val spmf) expression \<Rightarrow> 'mem instruction" where
  "Sample x e = SampleRaw (mk_var_untyped x) (map_spmf (some_embedding::'val\<Rightarrow>'mem) o e)"

type_synonym 'mem "program" = "'mem instruction list"

lift_definition update_var :: "('mem,'a) var \<Rightarrow> 'a \<Rightarrow> 'mem \<Rightarrow> 'mem" is
  "\<lambda>x a m. if valid_var (x, UNIV) then inv x (a, snd (x m)) else m".

lift_definition eval_var :: "('mem,'a) var \<Rightarrow> 'mem \<Rightarrow> 'a" is
  \<open>\<lambda>x m. if valid_var (x, UNIV) then fst (x m) else undefined\<close>.

lemma update_var_invalid: 
  fixes x :: "('mem,'a) var"
  assumes "\<not> has_variables TYPE('mem) TYPE('a)"
  shows "update_var x a m = m"
  apply (transfer fixing: m) 
  using assms by auto

lemma eval_var_invalid: 
  fixes x :: "('mem,'a) var"
  assumes "\<not> has_variables TYPE('mem) TYPE('a)"
  shows "eval_var x m = undefined"
proof (transfer fixing: m)
  fix x :: "'mem \<Rightarrow> 'a \<times> 'mem"
  from assms have "\<not> valid_var (x, UNIV)"
    by auto
  then show "(if valid_var (x, UNIV) then fst (x m) else undefined) = undefined"
    by simp
qed

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
  "\<lambda>(x,S) a m. if valid_var (x, S) then inv x (force_into a S, snd (x m)) else m".

lift_definition eval_untyped_var :: "'mem untyped_var \<Rightarrow> 'mem \<Rightarrow> 'mem" is
  \<open>\<lambda>(x,S) m. if valid_var (x, S) then fst (x m) else undefined\<close>.

lemma eval_untyped_var:
  fixes x :: "('mem,'val) var"
  shows "eval_untyped_var (mk_var_untyped x) m
       = (some_embedding::'val\<Rightarrow>'mem) (eval_var x m)"
proof (cases "has_variables TYPE('mem) TYPE('val)")
  case True
  define x' where "x' = mk_var_untyped x" (* Trick to make transfer insert facts about mk_var_untyped x *)
  then show ?thesis
    apply transfer by (auto simp: True mk_var_untyped_raw_def)
next
  case False
  define x' where "x' = mk_var_untyped x" (* Trick to make transfer insert facts about mk_var_untyped x *)
  then show ?thesis
    apply transfer by (auto simp: False mk_var_untyped_raw_def dummy_untyped_var_def)
qed

lemma update_untyped_var:
  fixes x :: "('mem,'val) var" and a :: 'val
  shows "update_untyped_var (mk_var_untyped x) ((some_embedding::'val\<Rightarrow>'mem) a) m
       = update_var x a m"
proof (cases "has_variables TYPE('mem) TYPE('val)")
  case True
  show ?thesis
  proof transfer
    fix x :: "'mem \<Rightarrow> 'val \<times> 'mem" and a m
    have valid_untyped: "valid_var (mk_var_untyped_raw x)"
      by (simp add: mk_var_untyped_raw_valid)
    assume \<open>has_variables TYPE('mem) TYPE('val) \<longrightarrow> valid_var (x, UNIV)\<close>
    with True have  valid: "valid_var (x, UNIV)" by simp
    then obtain R where bij_x: \<open>bij_betw x UNIV (UNIV \<times> R)\<close>
      unfolding valid_var_def by auto
    then have "inj x" 
      using bij_betw_def by blast
    define i where "i = (some_embedding::'val\<Rightarrow>'mem)"

    have "(map_prod i id \<circ> x) (inv x (a, snd (x m))) = (i a, snd (x m))"
      apply (auto)
      apply (subst bij_betw_inv_into_right[where f=x])
      using bij_x apply auto
      by (metis UNIV_I bij_betw_apply mem_Times_iff)
    then have "inv (map_prod i id \<circ> x) (i a, snd (x m)) = inv x (a, snd (x m))"
      apply (rule inv_f_eq[rotated])
      using \<open>inj x\<close> by (metis i_def inj_compose inv_id prod.inj_map some_embedding_inj surj_id surj_imp_inj_inv valid valid_var_less_eq_card)
    then show \<open>(case mk_var_untyped_raw x of
        (x, S) \<Rightarrow> \<lambda>a m. if valid_var (x, S) then inv x (force_into a S, snd (x m)) else m)
        (i a) m =
       (if valid_var (x, UNIV) then inv x (a, snd (x m)) else m)\<close>
      using valid_untyped valid by (simp add: mk_var_untyped_raw_def i_def)
  qed
next
  case False
  show ?thesis
  proof transfer
    fix x :: "'mem \<Rightarrow> 'val \<times> 'mem" and a m
        have valid_untyped: "valid_var (mk_var_untyped_raw x)"
      by (simp add: mk_var_untyped_raw_valid)
    from False have invalid: \<open>\<not> valid_var (x, UNIV)\<close>
      by auto
    show \<open>(case mk_var_untyped_raw x of
        (x, S) \<Rightarrow> \<lambda>a m. if valid_var (x, S) then inv x (force_into a S, snd (x m)) else m)
        (some_embedding a) m =
       (if valid_var (x, UNIV) then inv x (a, snd (x m)) else m)\<close>
      using valid_untyped by (simp add: invalid case_prod_beta mk_var_untyped_raw_def dummy_untyped_var_def)
  qed
qed

lemma eval_update_var[simp]:
  fixes m :: 'mem and a :: 'a
  assumes "has_variables TYPE('mem) TYPE('a)"
  shows \<open>eval_var x (update_var x a m) = a\<close>
proof (transfer, simp add: assms)
  fix x :: "'mem \<Rightarrow> 'a \<times> 'mem" and a::'a and m::'mem
  assume "valid_var (x, UNIV)"
  then obtain R where bij: "bij_betw x UNIV (UNIV \<times> R)"
    unfolding valid_var_def by auto
  show "fst (x (inv x (a, snd (x m)))) = a"
    apply (subst bij_betw_inv_into_right[where f=x])
    using bij apply auto
    by (metis UNIV_I bij_betw_apply mem_Times_iff)
qed

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
  assumes "\<not> has_variables TYPE('mem) TYPE('val)"
  shows "semantics1 (Set x e) m = return_spmf m"
proof (simp add: Set_def, transfer)
  fix x :: "'mem \<Rightarrow> 'val \<times> 'mem" and e :: "'mem\<Rightarrow>'val" and m :: 'mem
  from assms have invalid: "\<not> valid_var (x, UNIV)"
    unfolding has_variables_def by auto
  have \<open>inv (Pair (some_embedding ())) (force_into (some_embedding (e m)) {some_embedding ()}, m) = m\<close>
    using [[show_types, show_consts]]
    by auto
  with invalid show "(case mk_var_untyped_raw x of
        (x, S) \<Rightarrow> \<lambda>a m. if valid_var (x, S) then inv x (force_into a S, snd (x m)) else m)
        (some_embedding (e m)) m = m"
    unfolding dummy_untyped_var_def mk_var_untyped_raw_def by auto
qed

lemma semantics1_Sample_invalid:
  fixes x :: "('mem,'val) var" and a :: 'val
  assumes "\<not> has_variables TYPE('mem) TYPE('val)"
  shows "semantics1 (Sample x e) m = scale_spmf (weight_spmf (e m)) (return_spmf m)"
proof (simp add: Sample_def, transfer)
  fix x :: "'mem \<Rightarrow> 'val \<times> 'mem" and e :: "'mem\<Rightarrow>'val spmf" and m :: 'mem
  from assms have invalid: "\<not> valid_var (x, UNIV)"
    unfolding has_variables_def by auto
  have *: \<open>inv (Pair undefined) (force_into (some_embedding a) {undefined}, m) = m\<close> for a :: 'val
    using [[show_types, show_consts]]
    by auto
  with invalid show "map_spmf
        (\<lambda>a. (case mk_var_untyped_raw x of (x, S) \<Rightarrow> \<lambda>a m. if valid_var (x, S) then inv x (force_into a S, snd (x m)) else m) a m)
        (map_spmf some_embedding (e m)) =
       scale_spmf (weight_spmf (e m)) (return_spmf m)"
    using if_weak_cong[cong del]
    unfolding dummy_untyped_var_def mk_var_untyped_raw_def spmf.map_comp 
    by (auto simp: map_spmf_conv_bind_spmf bind_spmf_const o_def)
qed


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

definition postcondition_default2 :: "'mem1 program * 'mem2 program \<Rightarrow> ('mem1,'mem2) rinvariant \<Rightarrow> ('mem1,'mem2) rinvariant" where
  "postcondition_default2 = (\<lambda>(p1,p2) I m1 m2.
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
  assumes "\<lbrakk>SOLVER same_weight_tac?\<rbrakk> (\<And>m1 m2. A m1 m2 \<Longrightarrow> weight_spmf (semantics (fst p) m1) = weight_spmf (semantics (snd p) m2))"
  shows "rhoare A (fst p) (snd p) (postcondition_default2 p A)"
proof -
  obtain \<mu> 
    where \<mu>1: "map_spmf fst (\<mu> m1 m2) = semantics (fst p) m1"
      and \<mu>2: "map_spmf snd (\<mu> m1 m2) = semantics (snd p) m2" 
    if "A m1 m2" for m1 m2
    apply atomize_elim 
    using coupling_exists[OF assms[unfolded SOLVE_WITH_def, rule_format]]
    by (auto simp: all_conj_distrib[symmetric] intro!: choice)

  have supp: "m1' \<in> set_spmf (semantics (fst p) m1)" 
     "m2' \<in> set_spmf (semantics (snd p) m2)"
    if "(m1', m2') \<in> set_spmf (\<mu> m1 m2)" and "A m1 m2" for m1' m2' m1 m2
    unfolding \<mu>1[OF \<open>A m1 m2\<close>, symmetric] \<mu>2[OF \<open>A m1 m2\<close>, symmetric]
    using that by force+

  show ?thesis
    by (auto simp: postcondition_default2_def rhoare_def case_prod_beta pred_spmf_def intro!: rel_spmfI \<mu>1 \<mu>2 supp)
qed

lemma postcondition_rnd_valid:
  assumes p_def: "p = ([Sample x1 e1], [Sample x2 e2])"
  (* assumes "\<And>m1 m2. A m1 m2 \<Longrightarrow> map_spmf fst (\<mu> m1 m2) = semantics (fst p) m1" *)
  (* assumes "\<And>m1 m2. A m1 m2 \<Longrightarrow> map_spmf snd (\<mu> m1 m2) = semantics (snd p) m2" *)
  (* assumes "\<And>m1 m2. A m1 m2 \<Longrightarrow> set_spmf (\<mu> m1 m2) \<subseteq> j m1 m2" *)
  assumes fst: "\<And>m1 m2. A m1 m2 \<Longrightarrow> map_spmf fst (\<mu> m1 m2) = e1 m1"
  assumes snd: "\<And>m1 m2. A m1 m2 \<Longrightarrow> map_spmf snd (\<mu> m1 m2) = e2 m2"
  shows "rhoare A (fst p) (snd p) (postcondition_rnd \<mu> x1 x2 A)"
proof (unfold rhoare_def, rule, rule, rule)
  fix m1 m2 assume A: "A m1 m2"
  define \<mu>' where "\<mu>' = map_spmf (\<lambda>(v1, v2). (update_var x1 v1 m1, update_var x2 v2 m2)) (\<mu> m1 m2)"

  have "(m1', m2') \<in> set_spmf \<mu>' \<Longrightarrow> postcondition_rnd \<mu> x1 x2 A m1' m2'" for m1' m2'
    unfolding postcondition_rnd_def \<mu>'_def
    apply (rule exI[of _ m1], rule exI[of _ m2])
    using \<open>A m1 m2\<close> by auto

  moreover have "map_spmf fst \<mu>' = semantics (fst p) m1"
    unfolding \<mu>'_def p_def 
    by (simp add: fst[OF A, symmetric] spmf.map_comp o_def case_prod_beta)

  moreover have "map_spmf snd \<mu>' = semantics (snd p) m2"
    unfolding \<mu>'_def p_def 
    by (simp add: snd[OF A, symmetric] spmf.map_comp o_def case_prod_beta)

  ultimately show "rel_spmf (postcondition_rnd \<mu> x1 x2 A) (semantics (fst p) m1) (semantics (snd p) m2)"
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
proof (cases "has_variables TYPE('mem) TYPE('x)")
  case True
  show ?thesis
    apply transfer
    using True
    by (auto simp: bij_betw_imp_inj_on valid_var_def)
next
  case False
  then show ?thesis
    by (auto intro: update_var_invalid)
qed

lemma update_var_twice: 
  fixes x :: \<open>('mem,'x) var\<close>
  shows "update_var x a (update_var x b m) = update_var x a m"
proof (cases "has_variables TYPE('mem) TYPE('x)")
  case True
  show ?thesis
    apply transfer
    using True apply (auto simp: valid_var_def)
    by (metis SigmaD2 SigmaI UNIV_I bij_betw_imp_surj_on f_inv_into_f prod.collapse rangeI snd_conv)
next
  case False
  then show ?thesis
    by (auto simp: update_var_invalid valid_var_def)
qed

lemma independent_of_var[intro]:
  fixes x :: "('mem,'x) var" and y :: "('mem,'y) var"
  assumes "independent_vars x y"
  shows "independent_of (\<lambda>m. eval_var x m) y"
  unfolding independent_of_def independent_vars_def
proof (rule+, cases "has_variables TYPE('mem) TYPE('x)")
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
    using eval_var_invalid[OF False] by simp
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

(* We use \<longrightarrow> and not \<Longrightarrow> in invariant implications because
   otherwise applying a rule to an invariant implication subgoal 
   leaves too much freedom to Isabelle and Isabelle is not forced to
   match the "invariant m" part of the conclusion of the rule
 *)

lemma wp_generic[hoare_wp add]:
  fixes x :: "('mem,'val) var"
  assumes "invariant \<equiv> postcondition_default2 (p1,p2) A"
  assumes "\<And>m1 m2. A m1 m2 \<Longrightarrow> A' m1 m2"
  assumes "\<lbrakk>SOLVER wp_tac\<rbrakk> \<forall>m1 m2. postcondition_default2 (p1,p2) A' m1 m2 \<longrightarrow> B m1 m2"
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
  assumes "\<lbrakk>SOLVER wp_tac\<rbrakk> \<forall>mem1 mem2. postcondition_default2 (p1, p2) M mem1 mem2 \<longrightarrow> B mem1 mem2"
  shows "\<forall>mem1 mem2. postcondition_default2 (Set x e # p1, p2) (\<lambda>m1 m2. M (update_var x (e m1) m1) m2) mem1 mem2 \<longrightarrow> B mem1 mem2"
  using assms unfolding postcondition_default2_def
  by auto

lemma wp_Sample_cons1:
  assumes "\<lbrakk>SOLVER wp_tac\<rbrakk> \<forall>mem1 mem2. postcondition_default2 (p1, p2) M mem1 mem2 \<longrightarrow> B mem1 mem2"
  shows "\<forall>mem1 mem2. postcondition_default2 (Sample x e # p1, p2) 
               (\<lambda>m1 m2. \<forall>a\<in>set_spmf (e m1). M (update_var x a m1) m2) mem1 mem2 \<longrightarrow> B mem1 mem2"
  using assms unfolding postcondition_default2_def apply auto by blast

lemma wp_Set_cons2:
  assumes "\<lbrakk>SOLVER wp_tac\<rbrakk> \<forall>mem1 mem2. postcondition_default2 (p1, p2) M mem1 mem2 \<longrightarrow> B mem1 mem2"
  shows "\<forall>mem1 mem2. postcondition_default2 (p1, Set x e # p2) (\<lambda>m1 m2. M m1 (update_var x (e m2) m2)) mem1 mem2 \<longrightarrow> B mem1 mem2"
  using assms unfolding postcondition_default2_def
  by auto

lemma wp_Sample_cons2:
  assumes "\<lbrakk>SOLVER wp_tac\<rbrakk> \<forall>mem1 mem2. postcondition_default2 (p1, p2) M mem1 mem2 \<longrightarrow> B mem1 mem2"
  shows "\<forall>mem1 mem2. postcondition_default2 (p1, Sample x e # p2) 
               (\<lambda>m1 m2. \<forall>a\<in>set_spmf (e m2). M m1 (update_var x a m2)) mem1 mem2 \<longrightarrow> B mem1 mem2"
  using assms unfolding postcondition_default2_def apply auto by blast

lemma wp_skip12:
  shows "\<forall>mem1 mem2. postcondition_default2 ([], []) B mem1 mem2 \<longrightarrow> B mem1 mem2"
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
  assumes "invariant \<equiv> postcondition_default2 (P1,P2) A"
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

syntax "_expression_tmp_hoare" :: "'a \<Rightarrow> 'a" ("EXPR[_]")
syntax "_invariant_tmp_hoare" :: "'a \<Rightarrow> 'a" ("INV[_]")
syntax "_invariant2_tmp_hoare" :: "'a \<Rightarrow> 'a" ("INV2[_]")
hide_type (open) id
syntax "_variable_tmp_hoare" :: "id \<Rightarrow> 'a" ("$_" 1000)

ML_file \<open>tmp_hoare.ML\<close>

parse_translation \<open>let 
fun EXPR_like T ctxt [e] = Tmp_Hoare.tr_EXPR_like T ctxt e
fun EXPR2_like T ctxt [e] = Tmp_Hoare.tr_EXPR2_like T ctxt e
in
[
  (\<^syntax_const>\<open>_expression_tmp_hoare\<close>, EXPR_like dummyT),
  (\<^syntax_const>\<open>_invariant_tmp_hoare\<close>, EXPR_like HOLogic.boolT),
  (\<^syntax_const>\<open>_invariant2_tmp_hoare\<close>, EXPR2_like HOLogic.boolT)
] end\<close>

(* term "(INV2[$x1 = $x2], INV[$x = (1::nat)])" *)

nonterminal instruction_syntax_tmp_hoare
syntax "_instruction_set_tmp_hoare" :: "id \<Rightarrow> 'a \<Rightarrow> instruction_syntax_tmp_hoare" ("_ := _")
syntax "_instruction_sample_tmp_hoare" :: "id \<Rightarrow> 'a \<Rightarrow> instruction_syntax_tmp_hoare" ("_ <$ _")
syntax "_instruction_tmp_hoare" :: "instruction_syntax_tmp_hoare \<Rightarrow> 'a" ("INSTR[_]")
(* syntax "_string_of_identifier" :: "id \<Rightarrow> 'a" *)

translations "_instruction_tmp_hoare (_instruction_set_tmp_hoare x e)" 
          \<rightharpoonup> "CONST Set x (_expression_tmp_hoare e)"
translations "_instruction_tmp_hoare (_instruction_sample_tmp_hoare x e)" 
          \<rightharpoonup> "CONST Sample x (_expression_tmp_hoare e)"

print_translation \<open>[
(\<^const_syntax>\<open>Set\<close>, fn ctxt => fn [x,n] =>
  Const(\<^syntax_const>\<open>_instruction_tmp_hoare\<close>,dummyT) $
    (Const(\<^syntax_const>\<open>_instruction_set_tmp_hoare\<close>,dummyT) $ x $ n)
  handle TERM("dest_literal_syntax",_) => raise Match),

(\<^const_syntax>\<open>Sample\<close>, fn ctxt => fn [x,n] =>
  Const(\<^syntax_const>\<open>_instruction_tmp_hoare\<close>,dummyT) $
    (Const(\<^syntax_const>\<open>_instruction_sample_tmp_hoare\<close>,dummyT) $ x $ n)
  handle TERM("dest_literal_syntax",_) => raise Match)
]\<close>

term \<open>INSTR[x <$ return_spmf ($x+$y)]\<close>

nonterminal "program_syntax_tmp_hoare"
syntax "_program_cons_tmp_hoare" :: "instruction_syntax_tmp_hoare \<Rightarrow> program_syntax_tmp_hoare \<Rightarrow> program_syntax_tmp_hoare" ("_; _")
syntax "_program_single_tmp_hoare" :: "instruction_syntax_tmp_hoare \<Rightarrow> program_syntax_tmp_hoare" ("_")
syntax "_program_tmp_hoare" :: "program_syntax_tmp_hoare \<Rightarrow> 'a" ("PROG[_]")

translations "_program_tmp_hoare (_program_cons_tmp_hoare i is)" \<rightleftharpoons> "_instruction_tmp_hoare i # _program_tmp_hoare is"
translations "_program_tmp_hoare (_program_single_tmp_hoare i)" \<rightleftharpoons> "[_instruction_tmp_hoare i]"

term \<open>PROG[x := 0; x := $x+1]\<close>

end

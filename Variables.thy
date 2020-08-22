theory Variables
  imports Main "HOL-Library.Cardinality" Utils
  keywords "declare_variables" :: thy_goal and "get" and "set"
begin

definition "less_eq_card A B \<longleftrightarrow> (\<exists>f. inj_on f A \<and> range f \<subseteq> B)"

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

lemma valid_raw_varI':
  fixes R and g and s
  assumes "\<And>m a. g (s a m) = a"
  assumes "\<And>m. s (g m) m = m"
  assumes "\<And>m a b. s a (s b m) = s a m"
  shows "valid_raw_var (UNIV,g,s)"
  apply (rule valid_raw_varI) using assms by auto

lemma valid_raw_var_setget: "valid_raw_var (R,g,s) \<Longrightarrow> a\<in>R \<Longrightarrow> g (s a m) = a"
  and valid_raw_var_getset: "valid_raw_var (R,g,s) \<Longrightarrow> s (g m) m = m"
  and valid_raw_var_setset: "valid_raw_var (R,g,s) \<Longrightarrow> a\<in>R \<Longrightarrow> b\<in>R \<Longrightarrow> s a (s b m) = s a m"
  and valid_raw_var_rangeget: "valid_raw_var (R,g,s) \<Longrightarrow> range g = R"
  unfolding valid_raw_var_def by auto

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
    by (simp add: o_def)
next
  case False
  show "mk_var_untyped_raw (raw_dummy_var::('mem,'val) raw_var) = ({undefined}, raw_dummy_var)"
    using False
    by (auto simp: mk_var_untyped_raw_def case_prod_beta)
qed

lemma dummy_var_untyped[simp]: 
  "Rep_untyped_var (mk_var_untyped (dummy_var::('mem,'val) var)) = ({undefined},raw_dummy_var)"
  apply transfer by simp

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
  note disjE[consumes 1, case_names left right, cases pred] (* Not needed when importing MFMC_Misc *)
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
  note disjE[consumes 1, case_names left right, cases pred] (* Not needed when importing MFMC_Misc *)
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



definition "independent_of e x \<longleftrightarrow> (\<forall>m a. e m = e (update_var x a m))"

definition "independent_vars a b \<longleftrightarrow> (\<forall>x y mem.
   update_var b y (update_var a x mem) = update_var a x (update_var b y mem))"



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


lemma declare_variable_command_helper_valid:
  assumes "x \<equiv> Abs_var (g,s)"
  assumes "valid_raw_var (UNIV,g,s)"
  shows "valid_var x"
  by (simp add: Abs_var_inverse assms valid_var.rep_eq)

lemma declare_variable_command_helper_eval:
  assumes "x \<equiv> Abs_var (g,s)"
  assumes "valid_raw_var (UNIV,g,s)"
  shows "eval_var x m = g m"
  by (simp add: Abs_var_inverse assms eval_var.rep_eq)

lemma declare_variable_command_helper_update:
  assumes "x \<equiv> Abs_var (g,s)"
  assumes "valid_raw_var (UNIV,g,s)"
  shows "update_var x a m = s a m"
  by (simp add: Abs_var_inverse assms update_var.rep_eq)


lemma declare_variable_command_helper_indep:
  assumes "x \<equiv> Abs_var (gx,sx)"
  assumes "y \<equiv> Abs_var (gy,sy)"
  assumes "valid_raw_var (UNIV,gx,sx)"
  assumes "valid_raw_var (UNIV,gy,sy)"
  assumes "\<And>a b m. sx a (sy b m) = sy b (sx a m)"
  shows "independent_vars x y"
  unfolding independent_vars_def update_var.rep_eq assms(1,2)
  using assms(3-5) by (simp add: Abs_var_inverse)
  
lemma declare_variable_command_helper_indep_flip:
  assumes "x \<equiv> Abs_var (gx,sx)"
  assumes "y \<equiv> Abs_var (gy,sy)"
  assumes "valid_raw_var (UNIV,gx,sx)"
  assumes "valid_raw_var (UNIV,gy,sy)"
  assumes "\<And>a b m. sx a (sy b m) = sy b (sx a m)"
  shows "independent_vars y x"
  unfolding independent_vars_def update_var.rep_eq assms(1,2)
  using assms(3-5) by (simp add: Abs_var_inverse)

lemma declare_variable_command_helper_indep':
  assumes "x \<equiv> Abs_var (gx,sx)"
  assumes y: "y \<equiv> Abs_var (gy,sy)"
  assumes "valid_raw_var (UNIV,gx,sx)"
  assumes "valid_raw_var (UNIV,gy,sy)"
  assumes "\<And>a b m. sx a (sy b m) = sy b (sx a m)"
  shows "independent_of gy x"
proof -
  have "independent_of (eval_var y) x"
    apply (rule independent_of_var)
    using assms by (rule declare_variable_command_helper_indep_flip)
  then show ?thesis
    unfolding y eval_var.rep_eq
    apply (subst (asm) Abs_var_inverse)
    using assms by auto
qed

lemma declare_variable_command_helper_indep'_flip:
  assumes "x \<equiv> Abs_var (gx,sx)"
  assumes "y \<equiv> Abs_var (gy,sy)"
  assumes "valid_raw_var (UNIV,gx,sx)"
  assumes "valid_raw_var (UNIV,gy,sy)"
  assumes "\<And>a b m. sx a (sy b m) = sy b (sx a m)"
  shows "independent_of gx y"
  using assms(2,1,4,3) apply (rule declare_variable_command_helper_indep')
  using assms(5) by simp

ML_file "variables.ML"

end

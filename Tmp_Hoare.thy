theory Tmp_Hoare
  imports Main Forward_Hoare 
begin

section \<open>Programs\<close>

definition "less_eq_card A B \<longleftrightarrow> (\<exists>f. inj_on f A \<and> range f \<subseteq> B)"

type_synonym ('mem,'var) expression = \<open>'mem \<Rightarrow> 'var\<close>
type_synonym 'mem untyped_expression = \<open>('mem,'mem) expression\<close>

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

datatype 'mem instruction = SetRaw "'mem untyped_var" "'mem untyped_expression"
definition Set :: "('mem,'val) var \<Rightarrow> ('mem,'val) expression \<Rightarrow> 'mem instruction" where
  "Set x e = SetRaw (mk_var_untyped x) ((some_embedding::'val\<Rightarrow>'mem) o e)"

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
      using bij_betw_apply mem_Times_iff by fastforce
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
      using valid_untyped apply (simp add: invalid case_prod_beta mk_var_untyped_raw_def dummy_untyped_var_def)
      by (meson f_inv_into_f prod.inject rangeI)
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
    using bij_betw_apply mem_Times_iff by fastforce 
qed

section \<open>Semantics\<close>

fun semantics1 :: "'mem instruction \<Rightarrow> 'mem \<Rightarrow> 'mem" where
  "semantics1 (SetRaw x e) m = update_untyped_var x (e m) m"

lemma semantics1_Set[simp]:
  fixes x :: "('mem,'val) var" and a :: 'val
  shows "semantics1 (Set x e) m = update_var x (e m) m"
  unfolding Set_def apply simp
  by (rule update_untyped_var)

lemma semantics1_Set_invalid:
  fixes x :: "('mem,'val) var" and a :: 'val
  assumes "\<not> has_variables TYPE('mem) TYPE('val)"
  shows "semantics1 (Set x e) m = m"
proof (simp add: Set_def, transfer)
  fix x :: "'mem \<Rightarrow> 'val \<times> 'mem" and e :: "'mem\<Rightarrow>'val" and m :: 'mem
  from assms have invalid: "\<not> valid_var (x, UNIV)"
    unfolding has_variables_def by auto
  have \<open>inv (Pair (some_embedding ())) (force_into (some_embedding (e m)) {some_embedding ()}, m) = m\<close>
    using [[show_types, show_consts]]
    apply auto
    by (meson Pair_inject f_inv_into_f rangeI)
  with invalid show "(case mk_var_untyped_raw x of
        (x, S) \<Rightarrow> \<lambda>a m. if valid_var (x, S) then inv x (force_into a S, snd (x m)) else m)
        (some_embedding (e m)) m =
       m"
    unfolding dummy_untyped_var_def mk_var_untyped_raw_def by auto
qed

fun semantics :: "'mem program \<Rightarrow> 'mem \<Rightarrow> 'mem" where
  "semantics [] m = m"
| "semantics (c#p) m = semantics p (semantics1 c m)"

type_synonym 'mem "invariant" = "'mem \<Rightarrow> bool"

definition "hoare" :: "'mem invariant \<Rightarrow> 'mem program \<Rightarrow> 'mem invariant \<Rightarrow> bool" where
  "hoare A p B \<longleftrightarrow> (\<forall>m. A m \<longrightarrow> B (semantics p m))"

section \<open>Support for reasoning\<close>

definition postcondition_default :: "'mem program \<Rightarrow> 'mem invariant \<Rightarrow> 'mem invariant" where
  "postcondition_default p I m \<longleftrightarrow> (\<exists>m'. I m' \<and> m = semantics p m')"

lemma postcondition_default_valid:
  "hoare A p (postcondition_default p A)"
  unfolding postcondition_default_def hoare_def
  by auto

definition "independent_of e x \<longleftrightarrow> (\<forall>m a. e m = e (update_var x a m))"


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
       = update_var b (f mem) (update_var a (e mem) mem)"
      by (simp add: )
    have "e (update_var b (f mem) mem) = e mem"
      by (rule assms(2)[unfolded independent_of_def, rule_format, symmetric])
    then have 2: "semantics [Set b f, Set a e] mem
       = update_var a (e mem) (update_var b (f mem) mem)"
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
  assumes "instructions_commute a b"
  assumes "semantics (a#c) = semantics ac"
  shows "semantics (a#b#c) = semantics (b#ac)"
proof -
  have "semantics (a#b#c) = semantics c o (semantics1 b o semantics1 a)"
    by auto
  also have "semantics1 b o semantics1 a = semantics1 a o semantics1 b"
    using assms(1) by (simp add: semantics.simps[abs_def] o_def instructions_commute_def)
  also have "semantics c \<circ> (semantics1 a \<circ> semantics1 b) = (semantics c \<circ> semantics1 a) \<circ> semantics1 b"
    by auto
  also have "semantics c \<circ> semantics1 a = semantics ac"
    using assms(2) by (simp add: semantics.simps[abs_def] o_def)
  also have "semantics ac \<circ> semantics1 b = semantics (b#ac)"
    by auto
  finally show ?thesis
    by -
qed

ML \<open>
fun infer ctxt ts = 
  Drule.infer_instantiate' ctxt (ts |> map (Thm.cterm_of ctxt #> SOME))
\<close>

named_theorems independence

lemma independent_of_const[simp, independence]:
  shows "independent_of (\<lambda>m. a) x"
  unfolding independent_of_def by simp

lemma independent_of_split[independence, intro]:
  assumes "independent_of a x"
  assumes "independent_of b x"
  shows "independent_of (\<lambda>m. (a m) (b m)) x"
  using assms unfolding independent_of_def by auto

lemma update_var_current:
  fixes x :: \<open>('mem,'x) var\<close>
  shows "update_var x (eval_var x m) m = m"
  apply (cases "has_variables TYPE('mem) TYPE('x)")
   apply transfer
  by (auto intro: update_var_invalid simp: bij_betw_imp_inj_on valid_var_def)

lemma update_var_twice: 
  fixes x :: \<open>('mem,'x) var\<close>
  shows "update_var x a (update_var x b m) = update_var x a m"
  apply (cases "has_variables TYPE('mem) TYPE('x)")
   apply transfer
   apply (auto simp: update_var_invalid valid_var_def)
  by (metis UNIV_I bij_betw_apply bij_betw_inv_into_right mem_Sigma_iff old.prod.exhaust snd_conv)

lemma independent_of_var[independence, intro]:
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
  "semantics (p@q) = semantics q o semantics p"
  apply (rule ext, rename_tac m)
  by (induction p; simp)

lemma hoare_seq:
  assumes "hoare A p B"
  assumes "hoare B q C"
  shows "hoare A (p@q) C"
  using assms unfolding hoare_def semantics_seq by auto

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


lemma wp[hoare_wp add]: 
  fixes x :: "('mem,'val) var"
  assumes "invariant \<equiv> postcondition_default [Set x e] A"
  assumes imp: "\<And>m. A m \<Longrightarrow> B (update_var x (e m) m)"
  shows "\<And>m. invariant m \<longrightarrow> B m"
  using imp unfolding assms(1) postcondition_default_def by auto

lemma untouched[hoare_untouched add]: 
  fixes x :: "('mem,'val) var"
  assumes "invariant \<equiv> postcondition_default [Set x e] A"
  assumes indep: "independent_of B x"
  assumes imp: "\<And>m. A m \<Longrightarrow> B m"
  shows "\<And>m. invariant m \<longrightarrow> B m"
  using imp indep unfolding assms(1) postcondition_default_def independent_of_def 
  by (auto simp: semantics1_Set_invalid)

lemma updated[hoare_updated add]:
  fixes x :: "('mem,'val) var"
  assumes "invariant \<equiv> postcondition_default [Set x e] A"
  assumes [simp]: "has_variables TYPE('mem) TYPE('val)"
  assumes indep: "independent_of e x"
  shows "\<And>m. invariant m \<longrightarrow> eval_var x m = e m"
  using assms unfolding assms postcondition_default_def independent_of_def by auto

ML_file \<open>tmp_hoare.ML\<close>

subsection \<open>Concrete syntax for programs\<close>

syntax "_expression" :: "'a \<Rightarrow> 'a" ("EXPR[_]")
syntax "_invariant" :: "'a \<Rightarrow> 'a" ("INV[_]")
syntax "_variable" :: "id \<Rightarrow> 'a" ("$_")


parse_translation \<open>let 
fun make_syntax_type (Type(name, Ts)) = Term.list_comb 
  (Const("\<^type>"^name, dummyT), map make_syntax_type Ts)

fun EXPR_like T ctxt [e] =   let
  fun replace i (Const(\<^syntax_const>\<open>_variable\<close>,_) $ Free(n,_)) =
        @{const eval_var(dummy,dummy)} $ Free(n, dummyT) $ Bound i
    | replace i (Const(\<^syntax_const>\<open>_variable\<close>,_) $ _) = error "$ must precede an identifier"
    | replace i (t1$t2) = replace i t1 $ replace i t2
    | replace i (Abs(n,t,body)) = Abs(n,t,replace (i+1) body)
    | replace i t = t
  val e' = replace 0 e
  val t = Abs("mem",dummyT,e')
  in
    Const("_constrain", dummyT) $ t $ make_syntax_type (dummyT --> T)
  end
in
[
  (\<^syntax_const>\<open>_expression\<close>, EXPR_like dummyT),
  (\<^syntax_const>\<open>_invariant\<close>, EXPR_like HOLogic.boolT)
] end\<close>

nonterminal instruction_syntax
syntax "_instruction_set" :: "id \<Rightarrow> 'a \<Rightarrow> instruction_syntax" ("_ := _")
syntax "_instruction" :: "instruction_syntax \<Rightarrow> 'a" ("INSTR[_]")
(* syntax "_string_of_identifier" :: "id \<Rightarrow> 'a" *)

translations "_instruction (_instruction_set x e)" 
          \<rightharpoonup> "CONST Set x (_expression e)"

(* parse_translation \<open>[
("_string_of_identifier", fn ctxt => fn [Free(n,_)] => HOLogic.mk_literal n)]\<close> *)

(* ML \<open>
fun dest_bit_syntax (Const(\<^const_syntax>\<open>False\<close>,_)) = 0
  | dest_bit_syntax (Const(\<^const_syntax>\<open>True\<close>,_)) = 1
  | dest_bit_syntax _ = raise TERM ("dest_bit_syntax", []);

val dest_bits_syntax = Integer.eval_radix 2 o map dest_bit_syntax;

val dest_literal_syntax =
  let
    fun dest (Const (\<^const_syntax>\<open>Groups.zero_class.zero\<close>, _)) = []
      | dest (Const (\<^const_syntax>\<open>String.empty_literal\<close>, _)) = []
      | dest (Const (\<^const_syntax>\<open>String.Literal\<close>, _) $ b0 $ b1 $ b2 $ b3 $ b4 $ b5 $ b6 $ t) =
          chr (dest_bits_syntax [b0, b1, b2, b3, b4, b5, b6]) :: dest t
      | dest t = raise TERM ("dest_literal_syntax", [t]);
  in implode o dest end;
\<close> *)


print_translation \<open>[
(\<^const_syntax>\<open>Set\<close>, fn ctxt => fn [x,n] =>
  Const(\<^syntax_const>\<open>_instruction\<close>,dummyT) $
    (Const(\<^syntax_const>\<open>_instruction_set\<close>,dummyT) $ x $ n)
  handle TERM("dest_literal_syntax",_) => raise Match)
]\<close>

term \<open>INSTR[x := $x+$y]\<close>

nonterminal "program_syntax"
syntax "_program_cons" :: "instruction_syntax \<Rightarrow> program_syntax \<Rightarrow> program_syntax" ("_; _")
syntax "_program_single" :: "instruction_syntax \<Rightarrow> program_syntax" ("_")
syntax "_program" :: "program_syntax \<Rightarrow> 'a" ("PROG[_]")

translations "_program (_program_cons i is)" \<rightleftharpoons> "_instruction i # _program is"
translations "_program (_program_single i)" \<rightleftharpoons> "[_instruction i]"

term \<open>PROG[x := 0; x := $x+1]\<close>


end
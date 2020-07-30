theory Tmp_Hoare
  imports Main Forward_Hoare 
begin

section \<open>Programs\<close>

definition "less_eq_card A B \<longleftrightarrow> (\<exists>f. inj_on f A \<and> range f \<subseteq> B)"

type_synonym ('mem,'var) expression = \<open>'mem \<Rightarrow> 'var\<close>
type_synonym 'mem untyped_expression = \<open>('mem,'mem) expression\<close>

definition \<open>valid_var f S \<longleftrightarrow> (\<exists>R. bij_betw f UNIV (S \<times> R))\<close> 
definition "has_variables (_::'mem itself) (_::'val itself) \<longleftrightarrow> (\<exists>f::'mem\<Rightarrow>'val\<times>'mem. valid_var f UNIV)"

lemma has_variablesI[intro]: "valid_var (f::'mem\<Rightarrow>'val\<times>'mem) UNIV \<Longrightarrow> has_variables TYPE('mem) TYPE('val)"
  unfolding has_variables_def by auto

typedef ('mem,'val) var = "{f::'mem \<Rightarrow> 'val \<times> 'mem. has_variables TYPE('mem) TYPE('val) \<longrightarrow> valid_var f UNIV}"
  unfolding has_variables_def by auto
setup_lifting type_definition_var


definition "some_embedding = (SOME i::'a\<Rightarrow>'b. inj i)"

definition "dummy_untyped_var = (\<lambda>x::'mem. (some_embedding()::'mem,x), {some_embedding()::'mem})"
lemma dummy_untyped_var_valid: "dummy_untyped_var \<in> {(f, S). valid_var f S}"
  unfolding valid_var_def dummy_untyped_var_def apply auto
  apply (rule exI[of _ UNIV]) 
  apply (rule bij_betw_byWitness[of _ snd]) by auto

typedef 'mem untyped_var = 
  "{(f::'mem \<Rightarrow> 'mem \<times> 'mem, S). valid_var f S}"
  by (rule exI[of _ dummy_untyped_var], rule dummy_untyped_var_valid)
setup_lifting type_definition_untyped_var

lemma some_embedding_inj:
  assumes "less_eq_card (UNIV::'a set) (UNIV::'b set)"
  shows "inj (some_embedding::'a\<Rightarrow>'b)"
  unfolding some_embedding_def
  apply (rule someI_ex[of inj])
  using assms unfolding less_eq_card_def by auto

lemma valid_var_less_eq_card:
  assumes "valid_var (f::'a\<Rightarrow>'b\<times>'a) S"
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

lift_definition mk_var_untyped :: "('mem,'val) var \<Rightarrow> 'mem untyped_var" is
  \<open>\<lambda>f::'mem\<Rightarrow>'val \<times> 'mem. 
      (if valid_var f UNIV then
      (map_prod (some_embedding::'val\<Rightarrow>'mem) id \<circ> f,
       range (some_embedding::'val\<Rightarrow>'mem))
      else dummy_untyped_var)\<close>
  subgoal for f
proof (cases \<open>valid_var f UNIV\<close>)
  case False
  then show ?thesis
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
  then have \<open>valid_var (map_prod i id \<circ> f) (range i)\<close>
    unfolding valid_var_def by auto
  with True show ?thesis
    by (simp add: i_def)
qed done

lift_definition unit_var :: "('mem,unit) var" is "\<lambda>m. ((),m)"
  unfolding valid_var_def apply (rule exI[of _ UNIV])
  apply auto
  by (metis (mono_tags, hide_lams) bijI' old.unit.exhaust snd_conv surj_pair)

lemma unit_var_untyped: "Rep_untyped_var (mk_var_untyped unit_var) = dummy_untyped_var"
proof -
  have valid: "valid_var (Pair ()) UNIV"
    unfolding valid_var_def apply (rule exI[of _ UNIV])
    apply auto
    by (metis (mono_tags, hide_lams) bijI' old.unit.exhaust snd_conv surj_pair top_unit_def unit_var.rep_eq)
  show ?thesis
    apply transfer
    apply (simp add: valid dummy_untyped_var_def )
    unfolding dummy_untyped_var_def by auto
qed

datatype 'mem instruction = SetRaw "'mem untyped_var" "'mem untyped_expression"
definition Set :: "('mem,'val) var \<Rightarrow> ('mem,'val) expression \<Rightarrow> 'mem instruction" where
  "Set x e = SetRaw (mk_var_untyped x) ((some_embedding::'val\<Rightarrow>'mem) o e)"

type_synonym 'mem "program" = "'mem instruction list"

lift_definition update_var :: "('mem,'a) var \<Rightarrow> 'a \<Rightarrow> 'mem \<Rightarrow> 'mem" is
  "\<lambda>x a m. inv x (a, snd (x m))".

lift_definition eval_var :: "('mem,'a) var \<Rightarrow> 'mem \<Rightarrow> 'a" is
  \<open>\<lambda>x m. fst (x m)\<close>.

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
  "\<lambda>(x,S) a m. inv x (force_into a S, snd (x m))".

lift_definition eval_untyped_var :: "'mem untyped_var \<Rightarrow> 'mem \<Rightarrow> 'mem" is
  \<open>\<lambda>(x,S) m. fst (x m)\<close>.

lemma eval_untyped_var:
  fixes x :: "('mem,'val) var"
  assumes "has_variables TYPE('mem) TYPE('val)"
  shows "eval_untyped_var (mk_var_untyped x) m
       = (some_embedding::'val\<Rightarrow>'mem) (eval_var x m)"
  apply transfer using assms by auto

lemma update_untyped_var:
  fixes x :: "('mem,'val) var" and a :: 'val
  assumes "has_variables TYPE('mem) TYPE('val)"
  shows "update_untyped_var (mk_var_untyped x) ((some_embedding::'val\<Rightarrow>'mem) a) m
       = update_var x a m"
  apply transfer subgoal premises valid for x a m
proof -
  from assms valid have valid: "valid_var x UNIV" by auto
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
  then show ?thesis
    by (simp add: valid i_def)
qed done

lemma eval_update_var[simp]:
  fixes m :: 'mem and a :: 'a
  assumes "has_variables TYPE('mem) TYPE('a)"
  shows \<open>eval_var x (update_var x a m) = a\<close>
proof transfer
  fix x :: "'mem \<Rightarrow> 'a \<times> 'mem" and a::'a and m::'mem
  assume "has_variables TYPE('mem) TYPE('a) \<longrightarrow> valid_var x UNIV"
  with assms have "valid_var x UNIV"
    by simp
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
  assumes "has_variables TYPE('mem) TYPE('val)"
  shows "semantics1 (Set x e) m = update_var x (e m) m"
  unfolding Set_def apply simp
  using assms by (rule update_untyped_var)

lemma semantics1_Set_invalid:
  fixes x :: "('mem,'val) var" and a :: 'val
  assumes "\<not> has_variables TYPE('mem) TYPE('val)"
  shows "semantics1 (Set x e) m = m"
proof (simp add: Set_def, transfer)
  fix x :: "'mem \<Rightarrow> 'val \<times> 'mem" and e :: "'mem\<Rightarrow>'val" and m :: 'mem
  from assms have invalid: "\<not> valid_var x UNIV"
    unfolding has_variables_def by auto
  have \<open>inv (Pair (some_embedding ())) (force_into (some_embedding (e m)) {some_embedding ()}, m) = m\<close>
    using [[show_types, show_consts]]
    apply auto
    by (meson Pair_inject f_inv_into_f rangeI)
  with invalid show "(case if valid_var x UNIV then (map_prod some_embedding id \<circ> x, range some_embedding)
             else dummy_untyped_var of
        (x, S) \<Rightarrow> \<lambda>a m. inv x (force_into a S, snd (x m)))
        (some_embedding (e m)) m =
       m"
    unfolding dummy_untyped_var_def by auto
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
  consider (ab) "has_variables TYPE('mem) TYPE('a)" "has_variables TYPE('mem) TYPE('b)"
    | (not_a) "\<not> has_variables TYPE('mem) TYPE('a)"
    | (not_b) "\<not> has_variables TYPE('mem) TYPE('b)"
    by auto
  then have \<open>semantics [Set a e, Set b f] mem = semantics [Set b f, Set a e] mem\<close> for mem
  proof cases
    case ab
    have "f (update_var a (e mem) mem) = f mem"
      by (rule assms(1)[unfolded independent_of_def, rule_format, symmetric])
    then have 1: "semantics [Set a e, Set b f] mem
       = update_var b (f mem) (update_var a (e mem) mem)"
      by (simp add: ab)
    have "e (update_var b (f mem) mem) = e mem"
      by (rule assms(2)[unfolded independent_of_def, rule_format, symmetric])
    then have 2: "semantics [Set b f, Set a e] mem
       = update_var a (e mem) (update_var b (f mem) mem)"
      by (simp add: ab)
    show "semantics [Set a e, Set b f] mem = semantics [Set b f, Set a e] mem"
      unfolding 1 2
      using assms(3) unfolding independent_vars_def by simp
  next
    case not_a
    then have [simp]: "semantics1 (Set a e) m = m" for m
      by (rule semantics1_Set_invalid)
    then show \<open>semantics [Set a e, Set b f] mem = semantics [Set b f, Set a e] mem\<close>
      by simp
  next
    case not_b
    then have [simp]: "semantics1 (Set b f) m = m" for m
      by (rule semantics1_Set_invalid)
    then show \<open>semantics [Set a e, Set b f] mem = semantics [Set b f, Set a e] mem\<close>
      by simp
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

lemma independent_of_var[independence, intro]:
  assumes "independent_vars x y"
  shows "independent_of (\<lambda>m. eval_var x m) y"
  using assms 
  unfolding independent_of_def independent_vars_def
  apply transfer
  apply (thin_tac _)
  apply (thin_tac _)
  apply auto
  sorry

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
  assumes [simp]: "has_variables TYPE('mem) TYPE('val)"
  assumes imp: "\<And>m. A m \<Longrightarrow> B (update_var x (e m) m)"
  shows "\<And>m. invariant m \<longrightarrow> B m"
  using imp unfolding assms(1) postcondition_default_def by auto

lemma untouched[hoare_untouched add]: 
  fixes x :: "('mem,'val) var"
  assumes "invariant \<equiv> postcondition_default [Set x e] A"
  assumes indep: "independent_of B x"
  assumes imp: "\<And>m. A m \<Longrightarrow> B m"
  shows "\<And>m. invariant m \<longrightarrow> B m"
  apply (cases "has_variables TYPE('mem) TYPE('val)")
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

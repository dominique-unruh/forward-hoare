theory Reorder_Hoare
  imports Main Forward_Hoare 
begin

section \<open>Programs\<close>

type_synonym var = String.literal
type_synonym mem = \<open>var \<Rightarrow> int\<close>
type_synonym expression = \<open>mem \<Rightarrow> int\<close>
datatype instruction = Set var expression
type_synonym "program" = "instruction list"


section \<open>Semantics\<close>

fun semantics1 :: "instruction \<Rightarrow> mem \<Rightarrow> mem" where
  "semantics1 (Set x e) m = m(x:=e m)"

fun semantics :: "program \<Rightarrow> mem \<Rightarrow> mem" where
  "semantics [] m = m"
| "semantics (c#p) m = semantics p (semantics1 c m)"

type_synonym "invariant" = "mem \<Rightarrow> bool"

definition "hoare" :: "invariant \<Rightarrow> program \<Rightarrow> invariant \<Rightarrow> bool" where
  "hoare A p B \<longleftrightarrow> (\<forall>m. A m \<longrightarrow> B (semantics p m))"

section \<open>Support for reasoning\<close>

definition postcondition_default :: "program \<Rightarrow> invariant \<Rightarrow> invariant" where
  "postcondition_default p I m \<longleftrightarrow> (\<exists>m'. I m' \<and> m = semantics p m')"

lemma postcondition_default_valid:
  "hoare A p (postcondition_default p A)"
  unfolding postcondition_default_def hoare_def
  by auto


definition "independent_of B x = (\<forall>m1 m2. (\<forall>y\<noteq>x. m1 y = m2 y) \<longrightarrow> B m1 = B m2)"
lemma independent_ofI[intro]: 
  assumes "\<And>m1 m2. (\<And>y. y\<noteq>x \<Longrightarrow> m1 y = m2 y) \<Longrightarrow> B m1 = B m2"
  shows "independent_of B x"
  unfolding independent_of_def using assms by metis

lemma filter_literal_neq:
  assumes "String.Literal b0 b1 b2 b3 b4 b5 b6 cs \<noteq> String.Literal b0' b1' b2' b3' b4' b5' b6' cs'"
  shows "String.Literal b0 b1 b2 b3 b4 b5 b6 cs \<noteq> String.Literal b0' b1' b2' b3' b4' b5' b6' cs'"
  using assms by -

definition "instructions_commute a b \<longleftrightarrow> semantics [a,b] = semantics [b,a]"


lemma commute_indep:
  (* assumes "\<And>m1 m2. (\<And>y. y\<noteq>a \<Longrightarrow> m1 y = m2 y) \<Longrightarrow> f m1 = f m2" *)
  (* assumes "\<And>m1 m2. (\<And>y. y\<noteq>b \<Longrightarrow> m1 y = m2 y) \<Longrightarrow> e m1 = e m2" *)
  assumes "independent_of f a"
  assumes "independent_of e b"
  assumes "a \<noteq> b"
  (* shows "semantics [Set a e, Set b f] = semantics [Set b f, Set a e]" *)
  shows "instructions_commute (Set a e) (Set b f)"
proof (unfold instructions_commute_def, rule ext, rename_tac mem)
  fix mem
  have "f (mem(a := e mem)) = f mem"
    by (rule assms(1)[unfolded independent_of_def, rule_format], simp)
  then have 1: "semantics [Set a e, Set b f] mem = mem(a := e mem, b := f mem)"
    by simp
  have "e (mem(b := f mem)) = e mem"
    by (rule assms(2)[unfolded independent_of_def, rule_format], simp)
  then have 2: "semantics [Set b f, Set a e] mem = mem(b := f mem, a := e mem)"
    by simp
  show "semantics [Set a e, Set b f] mem = semantics [Set b f, Set a e] mem"
    unfolding 1 2
    using assms(3) by auto
qed

lemma insert_into_ordered_singleton_aux:
  "semantics [i] = semantics [i]"
  by simp

lemma insert_into_ordered_prepend_aux:
  "semantics (i#is) = semantics (i#is)"
  by simp

lemma insert_into_ordered_aux:
  (* assumes "semantics [a,b] = semantics [b,a]" *)
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

lemma independent_of_const:
  shows "independent_of (\<lambda>m. a) x"
  unfolding independent_of_def by simp

lemma independent_of_split:
  assumes "independent_of a x"
  assumes "independent_of b x"
  shows "independent_of (\<lambda>m. (a m) (b m)) x"
  using assms unfolding independent_of_def apply auto
  by metis

lemma independent_of_var:
  assumes "x \<noteq> y"
  shows "independent_of (\<lambda>m. m x) y"
  using assms unfolding independent_of_def by auto

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
  assumes "invariant \<equiv> postcondition_default [Set x e] A"
  assumes imp: "\<And>m. A m \<Longrightarrow> B (m(x:=e m))"
  shows "\<forall>m. invariant m \<longrightarrow> B m"
  using imp unfolding assms(1) postcondition_default_def by auto

lemma untouched[hoare_untouched add]:
  assumes "invariant \<equiv> postcondition_default [Set x e] A"
  assumes imp: "\<forall>m. A m \<longrightarrow> B m"
  assumes indep: "\<lbrakk>SOLVER independence_tac\<rbrakk> independent_of B x"
  shows "\<forall>m. invariant m \<longrightarrow> B m"
  using imp indep unfolding assms(1) postcondition_default_def independent_of_def 
  apply auto
  by (metis fun_upd_def)

lemma updated[hoare_updated add]:
  assumes "invariant \<equiv> postcondition_default [Set x e] A"
  assumes indep: "independent_of e x"
  shows "\<forall>m. invariant m \<longrightarrow> m x = e m"
  using assms unfolding assms postcondition_default_def independent_of_def by auto


ML_file \<open>reorder_hoare.ML\<close>

subsection \<open>Concrete syntax for programs\<close>

syntax "_expression_reorder_hoare" :: "'a \<Rightarrow> 'a" ("EXPR[_]")
syntax "_variable_reorder_hoare" :: "id \<Rightarrow> 'a" ("$_")

parse_translation \<open>[
  (\<^syntax_const>\<open>_expression_reorder_hoare\<close>, fn ctxt => fn [e] =>
  let
(*   fun vars (Free(n,_)) vs = vs
    | vars (Bound i) vs = vs
    | vars (Abs(n,_,body)) vs = vars body (n::vs)
    | vars (Const _) vs = vs
    | vars (Var _) vs = vs
    | vars (t1$t2) vs = vars t2 (vars t1 vs) *)
  (* val [mem] = Name.variant_list (vars e []) ["mem"] *)
  fun replace i (Const(\<^syntax_const>\<open>_variable_reorder_hoare\<close>,_) $ Free(n,_)) =
        (* Free(mem,dummyT) $ HOLogic.mk_literal n *)
        Bound i $ HOLogic.mk_literal n
    | replace i (Const(\<^syntax_const>\<open>_variable_reorder_hoare\<close>,_) $ _) = error "$ must precede an identifier"
    | replace i (t1$t2) = replace i t1 $ replace i t2
    | replace i (Abs(n,t,body)) = Abs(n,t,replace (i+1) body)
    | replace i t = t
  val e' = replace 0 e
  val t = Abs("mem",dummyT,e')
  val typ = (Const ("\<^type>fun", dummyT) $ Const ("\<^type>Reorder_Hoare.mem", dummyT) $
      Const ("\<^type>Int.int", dummyT))
  in
    Const("_constrain", dummyT) $ t $ typ
  end)
]\<close>

nonterminal instruction_syntax_reorder_hoare
syntax "_instruction_set_reorder_hoare" :: "id \<Rightarrow> 'a \<Rightarrow> instruction_syntax_reorder_hoare" ("_ := _")
syntax "_instruction_reorder_hoare" :: "instruction_syntax_reorder_hoare \<Rightarrow> 'a" ("INSTR[_]")
syntax "_string_of_identifier_reorder_hoare" :: "id \<Rightarrow> 'a"

translations "_instruction_reorder_hoare (_instruction_set_reorder_hoare x e)" \<rightharpoonup> "CONST Set (_string_of_identifier_reorder_hoare x) (_expression_reorder_hoare e)"

parse_translation \<open>[
(\<^syntax_const>\<open>_string_of_identifier_reorder_hoare\<close>, fn ctxt => fn [Free(n,_)] => HOLogic.mk_literal n)]\<close>

ML \<open>
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
\<close>


print_translation \<open>[
(\<^const_syntax>\<open>Set\<close>, fn ctxt => fn [str,n] =>
  Const(\<^syntax_const>\<open>_instruction_reorder_hoare\<close>,dummyT) $
    (Const(\<^syntax_const>\<open>_instruction_set_reorder_hoare\<close>,dummyT) $ Free(dest_literal_syntax str,dummyT) $ n)
  handle TERM("dest_literal_syntax",_) => raise Match)
]\<close>

term \<open>INSTR[x := $x+$y]\<close>

nonterminal "program_syntax_reorder_hoare"
syntax "_program_cons_reorder_hoare" :: "instruction_syntax_reorder_hoare \<Rightarrow> program_syntax_reorder_hoare \<Rightarrow> program_syntax_reorder_hoare" ("_; _")
syntax "_program_single_reorder_hoare" :: "instruction_syntax_reorder_hoare \<Rightarrow> program_syntax_reorder_hoare" ("_")
syntax "_program_reorder_hoare" :: "program_syntax_reorder_hoare \<Rightarrow> 'a" ("PROG[_]")

translations "_program_reorder_hoare (_program_cons_reorder_hoare i is)" \<rightleftharpoons> "_instruction_reorder_hoare i # _program_reorder_hoare is"
translations "_program_reorder_hoare (_program_single_reorder_hoare i)" \<rightleftharpoons> "[_instruction_reorder_hoare i]"

term \<open>PROG[x := 0; x := $x+1]\<close>

end

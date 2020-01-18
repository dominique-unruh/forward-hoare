theory Forward_Hoare
  imports "HOL-Library.Rewrite" "HOL-Eisbach.Eisbach" Main
  keywords "do" :: prf_decl % "proof"
begin

ML \<open>
fun def' binding t lthy =
  let val ((const,_),lthy) = Local_Theory.define ((binding,NoSyn),((Binding.suffix_name "_def" binding,[]),Thm.term_of t)) lthy
  in (const,lthy) end
fun def binding t lthy = def' binding t lthy |> snd
\<close>

section \<open>Programs\<close>
type_synonym var = String.literal
type_synonym mem = \<open>var \<Rightarrow> int\<close>
datatype instruction = Add var var | Set var int | Guess var
type_synonym program = "instruction list"

ML \<open>
type var = string
datatype instruction = Add of var*var | Set of var*int | Guess of var
type program = instruction list
fun instruction_to_term (Set (x, i)) = \<^const>\<open>Set\<close> $ HOLogic.mk_literal x $ HOLogic.mk_number HOLogic.intT i
  | instruction_to_term (Guess x) = \<^const>\<open>Guess\<close> $ HOLogic.mk_literal x
  | instruction_to_term (Add (x,y)) = \<^const>\<open>Add\<close> $ HOLogic.mk_literal x $ HOLogic.mk_literal y
fun program_to_term p = map instruction_to_term p |> HOLogic.mk_list \<^typ>\<open>instruction\<close>
fun program_to_cterm ctxt p = program_to_term p |> Thm.cterm_of ctxt
\<close>

section \<open>Invariants\<close>

datatype pc_spec1 = Trivial | Pick int
type_synonym pc_spec = "pc_spec1 list"
type_synonym invariant = "mem \<Rightarrow> bool"

fun postcondition1 :: "instruction \<Rightarrow> pc_spec1 \<Rightarrow> invariant \<Rightarrow> invariant option" where
  "postcondition1 (Set x i) Trivial I = Some (\<lambda>m. m x = i \<and> (\<exists>j. I (m(x:=j))))"
| "postcondition1 (Guess x) (Pick i) I = Some (\<lambda>m. m x = i \<and> (\<exists>j. I (m(x:=j))))"
| "postcondition1 (Guess x) Trivial I = Some (\<lambda>m. \<exists>j. I (m(x:=j)))"
| "postcondition1 (Add x y) Trivial I = (if x\<noteq>y then Some (\<lambda>m. I (m(x:=m x - m y))) else None)"
| "postcondition1 _ (Pick _) _ = None"

fun postcondition :: "program \<Rightarrow> pc_spec \<Rightarrow> invariant \<Rightarrow> invariant option" where
  "postcondition [] [] I = Some I"
| "postcondition (c#p) (s#ss) I = (case postcondition1 c s I of Some I' \<Rightarrow> postcondition p ss I' | None \<Rightarrow> None)"
| "postcondition _ _ _ = None"

lemma pc_length: "postcondition p1 pc1 I \<noteq> None \<Longrightarrow> length p1 = length pc1"
  apply (induction p1 arbitrary: I pc1)
  using list.exhaust apply force
  apply auto
  apply (case_tac pc1)
   apply auto
  by (metis option.case_eq_if option.distinct(1))


lemma postcondition': "postcondition (p @ [c]) (ss @ [s]) I =
  (case postcondition p ss I of Some I' \<Rightarrow> postcondition1 c s I' | None \<Rightarrow> None)"
proof (cases "length p = length ss")
  case True
  then show ?thesis
  proof (induction arbitrary: I rule:list_induct2)
    case Nil
    then show ?case
      apply (cases "postcondition1 c s I")
      by auto
  next
    case (Cons x xs y ys)
    show ?case 
      apply (cases "postcondition1 x y I"; simp)
      using Cons.IH by blast
  qed
next
  case False
  then show ?thesis
    by (metis length_append_singleton nat.inject option.simps(4) pc_length)
qed

ML \<open>
datatype pc_spec1 = Trivial | Pick of int
type pc_spec = pc_spec1 list
fun pc_spec1_to_term Trivial = \<^const>\<open>Trivial\<close>
  | pc_spec1_to_term (Pick i) = \<^const>\<open>Pick\<close> $ HOLogic.mk_number HOLogic.intT i
fun pc_spec_to_term pc = pc |> map pc_spec1_to_term |> HOLogic.mk_list \<^typ>\<open>pc_spec1\<close>
fun pc_spec_to_cterm ctxt pc = pc_spec_to_term pc |> Thm.cterm_of ctxt
fun merge_pc pc1 pc2 = SOME (pc1 @ pc2)
\<close>

section \<open>Ranges\<close>

ML \<open>
type range = int * int
fun valid_range (program:program) ((start,endd):range) =
  start <= endd andalso start >= 0 andalso endd <= length program
(* Contract: valid_range = true *)
fun extract_range (program:program) ((start,endd):range) : program =
  program |> drop start |> take (endd-start)
(* Contract: valid_range = true *)
fun merge_ranges (_:program) ((s1,e1):range) ((s2,e2):range) : range option =
  if e1=s2 then SOME (s1,e2) else NONE
\<close>

section \<open>Joint stuff\<close>

ML \<open>
type step_spec = {
  binding: binding,
  range: range,
  program_fragment: program,
  program_fragment_const: term,
  postcondition: pc_spec,
  postcondition_ct: cterm,
  postcondition_const: term,
  invariant_ct: cterm,
  invariant_const: term
}
\<close>

ML \<open>
fun mk_the t = let val oT = fastype_of t in case oT of 
  Type(\<^type_name>\<open>option\<close>,[T]) => Const(\<^const_name>\<open>the\<close>, oT --> T) $ t
 | _ => raise TYPE("mk_the: expected option type",[oT],[t]) end
\<close>


ML \<open>
structure Steps = Proof_Data (
  type T = step_spec Symtab.table
  fun init _ = Symtab.empty
)
\<close>

ML \<open>
fun add_spec spec = Steps.map (Symtab.update_new (Binding.name_of (#binding spec), spec))
fun get_spec name ctxt = Symtab.lookup (Steps.get ctxt) name |> the
\<close>


ML \<open>
fun make_step binding program range precondition_const postcondition lthy : local_theory = let
  fun bind suffix = Binding.suffix_name suffix binding
  val program_fragment = extract_range program range
  val program_fragment_ct = program_to_cterm lthy program_fragment
  val _ = tracing ("Program fragment: " ^ Syntax.string_of_term lthy (Thm.term_of program_fragment_ct))
  val (program_fragment_const,lthy) = 
      def' (bind "_prog") program_fragment_ct lthy
  val postcondition_ct = pc_spec_to_cterm lthy postcondition
  val _ = tracing ("Postcondition: " ^ Syntax.string_of_term lthy (Thm.term_of postcondition_ct))
  val (postcondition_const,lthy) = def' (bind "_pc") postcondition_ct lthy
  val invariant_opt_ct = \<^const>\<open>postcondition\<close> 
        $ program_fragment_const
        $ postcondition_const
        $ precondition_const |> Thm.cterm_of lthy
  val _ = tracing ("Invariant: " ^ Syntax.string_of_term lthy (Thm.term_of invariant_opt_ct))
  val (invariant_opt_const,lthy) = def' (bind "_inv_opt") invariant_opt_ct lthy
  val invariant_ct = invariant_opt_const |> mk_the |> Thm.cterm_of lthy
  val (invariant_const,lthy) = def' (bind "_inv") invariant_ct lthy
  val spec : step_spec = {binding=binding, range=range, program_fragment=program_fragment, invariant_const=invariant_const,
    invariant_ct=invariant_ct, postcondition=postcondition, 
    postcondition_const=postcondition_const, postcondition_ct=postcondition_ct,
    program_fragment_const=program_fragment_const}
  val _ = tracing ("Spec: " ^ \<^make_string> spec)
  val lthy = add_spec spec lthy
in
  lthy
end
\<close>

definition "pc_imp pc1 pc2 \<longleftrightarrow> (\<forall>m. pc1 m \<longrightarrow> pc2 m)"

section \<open>Experiments\<close>



ML \<open>
val test_prog = [Set ("x", 5), Guess "y", Add ("x", "y")] 
\<close>

definition "start_prog :: program \<equiv> []"
definition "start_pc :: pc_spec \<equiv> []"
definition "start_inv :: invariant \<equiv> \<lambda>m::mem. True"

ML \<open>
val start_spec : step_spec = {
  binding = \<^binding>\<open>start\<close>,
  range = (0,0),
  program_fragment = [],
  program_fragment_const = \<^term>\<open>start_prog\<close>,
  postcondition = [],
  postcondition_ct = \<^cterm>\<open>[]\<close>,
  postcondition_const = \<^term>\<open>start_pc\<close>,
  invariant_ct = \<^cterm>\<open>Some (\<lambda>m::mem. True)\<close>,
  invariant_const = \<^term>\<open>start_inv\<close>
}
\<close>


ML \<open>
fun do_cmd source = let
  val expr = ML_Context.expression (Input.pos_of source) (ML_Lex.read "Theory.local_setup (" @ ML_Lex.read_source source @ ML_Lex.read ")")
  in Context.proof_map expr |> Proof.map_context end
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>do\<close> "do something to the context in a proof"
    (Parse.ML_source >> (Toplevel.proof o do_cmd));
\<close>

lemma pc_impI[intro]: "(\<And>m. pc1 m \<Longrightarrow> pc2 m) \<Longrightarrow> pc_imp pc1 pc2"
  unfolding pc_imp_def by auto

lemma pc_impD[dest]: "pc_imp pc1 pc2 \<Longrightarrow> pc1 m \<Longrightarrow> pc2 m"
  unfolding pc_imp_def by auto


definition "independent_of (B::invariant) (x::var) = (\<forall>m1 m2. (\<forall>y\<noteq>x. m1 y = m2 y) \<longrightarrow> B m1 = B m2)"
lemma independent_ofI: 
  assumes "\<And>m1 m2. (\<And>y. y\<noteq>x \<Longrightarrow> m1 y = m2 y) \<Longrightarrow> B m1 = B m2"
  shows "independent_of B x"
  unfolding independent_of_def using assms by metis


lemma newvalue_Guess: 
  assumes "invariant \<equiv> the invariant_opt"
  assumes "invariant_opt \<equiv> postcondition prog pc A"
  assumes "prog \<equiv> [Guess x]"
  assumes "pc \<equiv> [Pick i]"
  shows "pc_imp invariant (\<lambda>m. m x = i)"
  unfolding assms(1-4)
  by (rule pc_impI; simp)

lemma newvalue_Set:
  assumes "invariant \<equiv> the invariant_opt"
  assumes "invariant_opt \<equiv> postcondition prog pc A"
  assumes "prog \<equiv> [Set x i]"
  assumes "pc \<equiv> [Trivial]"
  shows "pc_imp invariant (\<lambda>m. m x = i)"
  unfolding assms(1-4)
  by (rule pc_impI; simp)

lemmas newvalue = newvalue_Set newvalue_Guess

lemma unchanged_Guess: 
  assumes "invariant \<equiv> the invariant_opt"
  assumes "invariant_opt \<equiv> postcondition prog pc A"
  assumes "prog \<equiv> [Guess x]"
  assumes "pc \<equiv> [s]"
  assumes indep: "independent_of B x"
  assumes imp: "\<And>m. A m \<Longrightarrow> B m"
  shows "pc_imp invariant B"
  unfolding assms(1-4)
  apply (cases s; rule pc_impI; simp)
  using indep imp unfolding independent_of_def apply auto
  by (metis fun_upd_def)+

lemma unchanged_Add: 
  assumes "invariant \<equiv> the invariant_opt"
  assumes "invariant_opt \<equiv> postcondition prog pc A"
  assumes "prog \<equiv> [Add x y]"
  assumes "pc \<equiv> [Trivial]"
  assumes indep: "independent_of B x"
  assumes xy: "x \<noteq> y"
  assumes imp: "\<And>m. A m \<Longrightarrow> B m"
  shows "pc_imp invariant B"
  unfolding assms(1-4)
  apply (rule pc_impI)
  using indep imp xy unfolding independent_of_def apply auto
  by (metis fun_upd_def)

lemma unchanged_Set: 
  assumes "invariant \<equiv> the invariant_opt"
  assumes "invariant_opt \<equiv> postcondition prog pc A"
  assumes "prog \<equiv> [Set x i]"
  assumes "pc \<equiv> [Trivial]"
  assumes indep: "independent_of B x"
  assumes imp: "\<And>m. A m \<Longrightarrow> B m"
  shows "pc_imp invariant B"
  unfolding assms(1-4)
  apply (rule pc_impI)
  using indep imp unfolding independent_of_def apply auto
  by (metis fun_upd_def)

lemmas unchanged = unchanged_Guess unchanged_Add unchanged_Set

lemma wp_Add: 
  assumes "invariant \<equiv> the invariant_opt"
  assumes "invariant_opt \<equiv> postcondition prog pc A"
  assumes "prog \<equiv> [Add x y]"
  assumes "pc \<equiv> [Trivial]"
  assumes distinct: "x \<noteq> y"
  assumes imp: "\<And>m. A m \<Longrightarrow> B (m(x:=m x + m y))"
  shows "pc_imp invariant B"
  unfolding assms(1-4)
  apply (rule pc_impI)
  using distinct apply simp apply (drule imp)
  by auto

lemma wp_Set:
  assumes "invariant \<equiv> the invariant_opt"
  assumes "invariant_opt \<equiv> postcondition prog pc A"
  assumes "prog \<equiv> [Set x i]"
  assumes "pc \<equiv> [Trivial]"
  assumes imp: "\<And>m. A m \<Longrightarrow> B (m(x:=i))"
  shows "pc_imp invariant B"
  unfolding assms(1-4)
  apply (rule pc_impI)
  apply simp
  using imp
  apply auto
  apply (drule imp)
  by auto

lemmas wp = wp_Add wp_Set

lemma valid_Add:
  fixes inv
  assumes "inv \<equiv> postcondition prog pc A"
  assumes "prog \<equiv> [Add x y]"
  assumes "pc \<equiv> [Trivial]"
  assumes distinct: "x \<noteq> y"
  shows "inv \<noteq> None"
  unfolding assms(1-3) using distinct by simp


lemma valid_Set:
  fixes inv
  assumes "inv \<equiv> postcondition prog pc A"
  assumes "prog \<equiv> [Set x i]"
  assumes "pc \<equiv> [Trivial]"
  shows "inv \<noteq> None"
  unfolding assms(1-3) by simp

lemma valid_Guess:
  fixes inv
  assumes "inv \<equiv> postcondition prog pc A"
  assumes "prog \<equiv> [Guess x]"
  assumes "pc \<equiv> [s]"
  shows "inv \<noteq> None"
  unfolding assms(1-3) apply (cases s) by simp_all

lemmas valid = valid_Set valid_Guess valid_Add

ML \<open>
fun use_facts_tac ctxt thms = 
  EVERY' (map (fn thm => forward_tac ctxt [thm COMP @{thm pc_impD}]) (rev (tl thms)))
  THEN' (dresolve_tac ctxt [hd thms COMP @{thm pc_impD}])
\<close>

(* method use_fact uses fact = frule fact[THEN pc_impD] *)

lemma list_rev_induct2 [consumes 1, case_names Nil snoc]:
  "length xs = length ys \<Longrightarrow> P [] [] \<Longrightarrow>
   (\<And>x xs y ys. length xs = length ys \<Longrightarrow> P xs ys \<Longrightarrow> P (xs@[x]) (ys@[y]))
   \<Longrightarrow> P xs ys"
  apply (rule list_induct2[where xs="rev xs" and ys="rev ys" and P="\<lambda>xs ys. P (rev xs) (rev ys)", simplified])
  by auto

lemma pc_merge:
  assumes "postcondition p1 pc1 I \<noteq> None"
  shows "postcondition p2 pc2 (the (postcondition p1 pc1 I)) = postcondition (p1 @ p2) (pc1 @ pc2) I"
  using assms
proof (cases "length p2 = length pc2")
  case True
  then show ?thesis
  proof (induction rule:list_rev_induct2)
    case Nil
    then show ?case
      using assms by simp
  next
    case (snoc p2s p2 pc2s pc2)
    show ?case
      unfolding append_assoc[symmetric] postcondition'
      by (simp add: snoc.IH)
  qed
next
  case False
  then have 1: "postcondition p2 pc2 I' = None" for I'
    using pc_length by blast
  from assms have "length p1 = length pc1"
    by (rule pc_length)
  with False have "length (p1@p2) \<noteq> length (pc1@pc2)"
    by auto
  then have 2: "postcondition (p1 @ p2) (pc1 @ pc2) I = None"
    using pc_length by blast
  from 1 2 
  show ?thesis
    by simp
qed

fun semantics1 :: "instruction \<Rightarrow> mem \<Rightarrow> mem set" where
  "semantics1 (Set x i) m = {m(x:=i)}"
| "semantics1 (Add x y) m = {m(x:=m x + m y)}"
| "semantics1 (Guess x) m = {m(x:=i)| i. True}"

fun semantics :: "program \<Rightarrow> mem \<Rightarrow> mem set" where
  "semantics [] m = {m}"
| "semantics (c#p) m = (\<Union>m'\<in>semantics1 c m. semantics p m')"

definition hoare :: "invariant \<Rightarrow> program \<Rightarrow> invariant \<Rightarrow> bool" where
  "hoare A p B \<longleftrightarrow> (\<forall>m. A m \<longrightarrow> (\<exists>m'\<in>semantics p m. B m'))"

lemma hoare_skip[simp]: "hoare A [] A"
  unfolding hoare_def by auto

lemma hoare_cons: 
  assumes "hoare A [c] B"
  assumes "hoare B p C"
  shows "hoare A (c#p) C"
  using assms unfolding hoare_def apply auto by metis

lemma hoareI1:
  assumes "postcondition1 c s A = Some C"
  shows "hoare A [c] C"
proof (cases c)
  case (Add x y)
  show ?thesis
    unfolding Add
  proof (cases s)
    case Trivial
    show "hoare A [Add x y] C"
      using assms 
      unfolding hoare_def Add Trivial
      apply auto
      by (smt fun_upd_other fun_upd_same fun_upd_triv fun_upd_upd option.distinct(1) option.inject)
  next
    case (Pick i)
    with assms Add have False
      by simp
    then show "hoare A [Add x y] C"
      by simp
  qed
next
  case (Set x i)
  show ?thesis
    unfolding Set
  proof (cases s)
    case Trivial
    show "hoare A [Set x i] C"
      using assms 
      unfolding hoare_def Set Trivial
      apply auto
      by (metis fun_upd_triv)
  next
    case (Pick j)
    with assms Set have False
      by simp
    then show "hoare A [Set x i] C"
      by simp
  qed
next
  case (Guess x)
  show ?thesis
    unfolding Guess
  proof (cases s)
    case (Pick j)
    show "hoare A [Guess x] C"
      using assms 
      unfolding hoare_def Guess Pick
      apply simp
      by (metis (mono_tags, lifting) fun_upd_idem_iff fun_upd_same fun_upd_upd)
  next
    case Trivial
    show "hoare A [Guess x] C"
      using assms 
      unfolding hoare_def Guess Trivial
      apply simp
      by (metis fun_upd_triv)
  qed
qed

lemma hoareI0:
  assumes "postcondition p pc A = Some B"
  shows "hoare A p B"
proof -
  have "length p = length pc"
    using assms pc_length by auto
  from this assms show ?thesis
  proof (induction arbitrary: A rule:list_induct2)
    case Nil
    then show ?case by simp
  next
    case (Cons c p s pc)
    then have "postcondition (c # p) (s # pc) A = Some B"
      by -
    then obtain C where pc_p: "postcondition p pc C = Some B" and pc_c: "postcondition1 c s A = Some C"
      apply (cases "postcondition1 c s A")
      by auto
    from pc_p have "hoare C p B"
      using Cons.IH by auto
    moreover from pc_c have "hoare A [c] C"
      by (rule hoareI1)
    ultimately show ?case
      apply (rule_tac hoare_cons) by auto
  qed
qed

lemma hoare_conseq:
  assumes "pc_imp A A'"
  assumes "pc_imp B' B"
  assumes "hoare A' p B'"
  shows "hoare A p B"
  using assms unfolding hoare_def pc_imp_def by blast

lemma hoareI:
  assumes "B' \<equiv> postcondition p' pc A'"
  assumes "B' \<noteq> None"
  assumes AA': "pc_imp A A'"
  assumes B'B: "pc_imp (the B') B"
  assumes p'p: "p' = p"
  shows "hoare A p B"
  using AA' B'B apply (rule hoare_conseq)
  apply (rule hoareI0)
  using assms(1-2) unfolding p'p by auto

lemma True
proof 

  define prog where "prog = [Set STR ''x'' 5, Guess STR ''y'', Add STR ''x'' STR ''y'']"

  (* Step 1 *)

  do \<open>make_step \<^binding>\<open>step1\<close> test_prog (0,1) (#invariant_const start_spec) [Trivial]\<close>

  have step1_exists: "step1_inv_opt \<noteq> None"
    by (rule valid, fact step1_inv_opt_def, fact step1_prog_def, fact step1_pc_def)

  have step1_x5: "pc_imp step1_inv (\<lambda>m. m STR ''x'' = 5)"
    by (rule newvalue, fact step1_inv_def, fact step1_inv_opt_def, fact step1_prog_def, fact step1_pc_def)

  (* Step 2 *)

  do \<open>make_step \<^binding>\<open>step2\<close> test_prog (1,2) (#invariant_const (get_spec "step1" \<^context>)) [Pick ~5]\<close>

  have step2_exists: "step2_inv_opt \<noteq> None"
    by (rule valid, fact step2_inv_opt_def, fact step2_prog_def, fact step2_pc_def)

  have step2_x5: "pc_imp step2_inv (\<lambda>m. m STR ''x'' = 5)"
    apply (rule unchanged, fact step2_inv_def, fact step2_inv_opt_def, fact step2_prog_def, fact step2_pc_def)
     apply (rule independent_ofI, simp)
    apply (tactic \<open>use_facts_tac \<^context> @{thms step1_x5} 1\<close>)
    by simp

  have step2_y5: "pc_imp step2_inv (\<lambda>m. m STR ''y'' = -5)"
    by (rule newvalue, fact step2_inv_def, fact step2_inv_opt_def, fact step2_prog_def, fact step2_pc_def)

  ML_prf \<open>
    local
    val ctxt = \<^context>
    val step1 = get_spec "step1" ctxt
    val step2 = get_spec "step2" ctxt
    in
      val range = merge_ranges test_prog (#range step1) (#range step2) |> the
      val pc = merge_pc (#postcondition step1) (#postcondition step2) |> the
    end
  \<close>

  have start_step2: "step2_inv_opt = postcondition (step1_prog @ step2_prog) (step1_pc @ step2_pc) start_inv"
    using step1_exists
    unfolding step2_inv_opt_def step1_inv_def step1_inv_opt_def
    by (rule pc_merge)

  (* Step 3 *)

  do \<open>make_step \<^binding>\<open>step3\<close> test_prog (2,3) (#invariant_const (get_spec "step2" \<^context>)) [Trivial]\<close>

  have step3_exists: "step3_inv_opt \<noteq> None"
    apply (rule valid, fact step3_inv_opt_def, fact step3_prog_def, fact step3_pc_def)
    by simp

  have step3_y5: "pc_imp step3_inv (\<lambda>m. m STR ''y'' = -5)"
    apply (rule unchanged, fact step3_inv_def, fact step3_inv_opt_def, fact step3_prog_def, fact step3_pc_def)
      apply (rule independent_ofI, simp)
     apply simp
    apply (tactic \<open>use_facts_tac \<^context> @{thms step2_y5} 1\<close>)
    by simp

  have step3_x0: "pc_imp step3_inv (\<lambda>m. m STR ''x'' = 0)"
    apply (rule wp_Add, fact step3_inv_def, fact step3_inv_opt_def, fact step3_prog_def, fact step3_pc_def)
     apply simp
    apply (tactic \<open>use_facts_tac \<^context> @{thms step2_x5 step2_y5} 1\<close>)
    by simp

  have start_step3: "step3_inv_opt \<equiv> postcondition ((step1_prog @ step2_prog) @ step3_prog) ((step1_pc @ step2_pc) @ step3_pc) start_inv"
    apply (subst pc_merge[symmetric])
    using start_step2 step2_inv_opt_def step2_pc_def step2_prog_def apply force
    unfolding step3_inv_opt_def step3_inv_def start_step2[symmetric] step2_inv_def
    by simp

  then have "hoare (\<lambda>_. True) prog (\<lambda>m. m STR ''x'' = 0)"
    apply (rule hoareI)
       apply (fact step3_exists)
      apply (force simp: start_inv_def)
    using step3_x0 step3_inv_def apply simp
    unfolding step1_prog_def step2_prog_def step3_prog_def prog_def
    by simp
qed


end

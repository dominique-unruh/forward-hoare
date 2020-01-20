theory Forward_Hoare
  imports "HOL-Library.Rewrite" "HOL-Eisbach.Eisbach" Main
  keywords "do" :: prf_decl % "proof"
    and "do_prf" :: prf_goal % "proof"
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

type_synonym invariant = "mem \<Rightarrow> bool"

fun postcondition_trivial :: "instruction \<Rightarrow> invariant \<Rightarrow> invariant" where
  "postcondition_trivial (Set x i) I = (\<lambda>m. m x = i \<and> (\<exists>j. I (m(x:=j))))"
| "postcondition_trivial (Guess x) I = (\<lambda>m. \<exists>j. I (m(x:=j)))"
| "postcondition_trivial (Add x y) I = (\<lambda>m. I (m(x:=m x - m y)))"

fun postcondition_pick :: "instruction \<Rightarrow> int \<Rightarrow> invariant \<Rightarrow> invariant" where
  "postcondition_pick (Guess x) i I = (\<lambda>m. m x = i \<and> (\<exists>j. I (m(x:=j))))"
| "postcondition_pick _ _ _ = undefined"

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
type invariant = {
  binding: binding,
  cterm: cterm,
  const: term
}
\<close>


ML \<open>
type hoare = {
  binding: binding,
  range: range,
  program_fragment: program,
  program_fragment_const: term,
  precondition: string,
  postcondition: string,
  valid: thm
}
\<close>

ML \<open>
structure Hoare_Data = Proof_Data (
  type T = { invariants: invariant Symtab.table,
             hoares: hoare Symtab.table }
  fun init _ = { invariants=Symtab.empty, hoares=Symtab.empty }
)
\<close>


ML \<open>
fun mk_the t = let val oT = fastype_of t in case oT of 
  Type(\<^type_name>\<open>option\<close>,[T]) => Const(\<^const_name>\<open>the\<close>, oT --> T) $ t
 | _ => raise TYPE("mk_the: expected option type",[oT],[t]) end
\<close>

ML \<open>
fun map_invariants f = Hoare_Data.map (fn {invariants,hoares} => {invariants=f invariants, hoares=hoares})
fun map_hoares f = Hoare_Data.map (fn {invariants,hoares} => {invariants=invariants, hoares=f hoares})
fun add_invariant0 i = map_invariants (Symtab.update_new (Binding.name_of (#binding i), i))
fun add_hoare0 i = map_hoares (Symtab.update_new (Binding.name_of (#binding i), i))
fun get_invariant ctxt name = Symtab.lookup (Hoare_Data.get ctxt |> #invariants) name
fun get_hoare ctxt name = Symtab.lookup (Hoare_Data.get ctxt |> #hoares) name
\<close>

ML \<open>
fun add_invariant binding invariant ctxt : invariant * Proof.context = let
  fun bind suffix = Binding.suffix_name suffix binding
  val _ = tracing ("Adding invariant "^ Pretty.string_of (Binding.pretty binding) ^ ": " ^ Syntax.string_of_term ctxt (Thm.term_of invariant))
  val (invariant_const,ctxt) = def' (bind "_inv") invariant ctxt
  val info : invariant = {binding=binding, const=invariant_const, cterm=invariant}
  val ctxt = add_invariant0 info ctxt
  in (info,ctxt) end
\<close>

ML \<open>
fun add_hoare1 binding program range (precondition:invariant) (postcondition:invariant) ctxt = let
  fun bind suffix = Binding.suffix_name suffix binding
  val program_fragment = extract_range program range
  val program_fragment_ct = program_to_cterm ctxt program_fragment
  val _ = tracing ("Program fragment: " ^ Syntax.string_of_term ctxt (Thm.term_of program_fragment_ct))
  val (program_fragment_const,ctxt) = 
      def' (bind "_prog") program_fragment_ct ctxt
  val info : hoare = {binding=binding, range=range,
    precondition=Binding.name_of (#binding precondition),
    postcondition=Binding.name_of (#binding postcondition),
    program_fragment=program_fragment, program_fragment_const=program_fragment_const,
    valid= @{thm TrueI}
  }
  (* val ctxt = add_hoare0 info ctxt *)
  in (info,ctxt) end
\<close>


definition "pc_imp pc1 pc2 \<longleftrightarrow> (\<forall>m. pc1 m \<longrightarrow> pc2 m)"

section \<open>Experiments\<close>

ML \<open>
structure Do_Prf = Proof_Data(
  type T = Proof.state -> Proof.state
  fun init _ = fn _ => error "don't call this"
)
\<close>

ML \<open>
val test_prog = [Set ("x", 5), Guess "y", Add ("x", "y")] 
\<close>

ML \<open>
fun do_prf_cmd source state = let
  val expr = ML_Context.expression (Input.pos_of source) 
    (ML_Lex.read "Context.>> (Context.map_proof (Do_Prf.put (" @ ML_Lex.read_source source @ ML_Lex.read ")))")
  val f = Context.proof_map expr (Proof.context_of state) |> Do_Prf.get
  val state = f state
  in state end

fun do_cmd source = let
  val expr = ML_Context.expression (Input.pos_of source) (ML_Lex.read "Theory.local_setup (" @ ML_Lex.read_source source @ ML_Lex.read ")")  
  in Context.proof_map expr |> Proof.map_context end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>do\<close> "do something to the context in a proof"
    (Parse.ML_source >> (Toplevel.proof o do_cmd));
  Outer_Syntax.command \<^command_keyword>\<open>do_prf\<close> "do something to the context in a proof"
    (Parse.ML_source >> (Toplevel.proof o do_prf_cmd));
\<close>

ML \<open>
  fun prove binding after_qed prop state = 
Proof.have true NONE after_qed [] [] [((binding,[]),[(prop,[])])] true state |> \<^print> |> snd
\<close>


lemma False
proof -
  do_prf \<open>fn state => let 
fun after_qed (ctxt,thms) state = state
val state = prove \<^binding>\<open>xxxx\<close> after_qed \<^prop>\<open>1=1\<close> state
in state end
\<close>
    by auto
  thm xxxx
  oops

lemma pc_impI[intro]: "(\<And>m. pc1 m \<Longrightarrow> pc2 m) \<Longrightarrow> pc_imp pc1 pc2"
  unfolding pc_imp_def by auto

lemma pc_impD[dest]: "pc_imp pc1 pc2 \<Longrightarrow> pc1 m \<Longrightarrow> pc2 m"
  unfolding pc_imp_def by auto


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

lemma hoareI:
  assumes "\<And>m. A m \<Longrightarrow> Bex (semantics p m) B"
  shows "hoare A p B"
  unfolding hoare_def using assms by simp

lemma valid_Add:
  assumes "B \<equiv> postcondition_trivial (Add x y) A"
  assumes "p \<equiv> [Add x y]"
  assumes distinct: "x \<noteq> y"
  shows "hoare A p B"
  apply (rule hoareI)
  unfolding assms(1-2) using distinct by simp


lemma valid_Set:
  assumes "B \<equiv> postcondition_trivial (Set x i) A"
  assumes "p \<equiv> [Set x i]"
  shows "hoare A p B"
  apply (rule hoareI)
  unfolding assms
  apply simp
  by (metis fun_upd_triv)

lemma valid_Guess_trivial:
  assumes "B \<equiv> postcondition_trivial (Guess x) A"
  assumes "p == [Guess x]"
  shows "hoare A p B"
  apply (rule hoareI)
  unfolding assms
  apply simp
  by (metis fun_upd_triv)

lemma valid_Guess_pick:
  assumes "B \<equiv> postcondition_pick (Guess x) i A"
  assumes "p == [Guess x]"
  shows "hoare A p B"
  apply (rule hoareI)
  unfolding assms
  apply (rule bexI[of _ "_(x := i)"])
  apply auto
  by (metis fun_upd_triv)

lemmas valid = valid_Set valid_Guess_pick valid_Guess_trivial valid_Add

ML \<open>
fun use_facts_tac ctxt thms = 
  EVERY' (map (fn thm => forward_tac ctxt [thm COMP @{thm pc_impD}]) (rev (tl thms)))
  THEN' (dresolve_tac ctxt [hd thms COMP @{thm pc_impD}])
\<close>

lemma list_rev_induct2 [consumes 1, case_names Nil snoc]:
  "length xs = length ys \<Longrightarrow> P [] [] \<Longrightarrow>
   (\<And>x xs y ys. length xs = length ys \<Longrightarrow> P xs ys \<Longrightarrow> P (xs@[x]) (ys@[y]))
   \<Longrightarrow> P xs ys"
  apply (rule list_induct2[where xs="rev xs" and ys="rev ys" and P="\<lambda>xs ys. P (rev xs) (rev ys)", simplified])
  by auto

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

ML \<open>
fun hoare_thm ctxt (hoare:hoare) : cterm = let
  (* val hoare = get_hoare ctxt hoare |> the *)
  val pre = #precondition hoare |> get_invariant ctxt |> the |> #const
  val post = #postcondition hoare |> get_invariant ctxt |> the |> #const
  val prog = #program_fragment_const hoare
  val prop = \<^const>\<open>hoare\<close> $ pre $ prog $ post |> HOLogic.mk_Trueprop
  in Thm.cterm_of ctxt prop end
\<close>

ML \<open>
fun update_hoare_valid new_valid ({binding, range, program_fragment, program_fragment_const, precondition,
  postcondition, valid=_}:hoare) : hoare =
 {binding=binding, range=range, program_fragment=program_fragment,
  program_fragment_const=program_fragment_const, precondition=precondition,
  postcondition=postcondition,
  valid=new_valid}
\<close>


ML \<open>
fun add_hoare2 binding program range (precondition:invariant) (postcondition:invariant) state : hoare * Proof.state = let
  val (info,state) = Proof.map_context_result (add_hoare1 binding program range precondition postcondition) state
  fun after_qed (_,[[valid]]) = Proof.map_context (add_hoare0 (update_hoare_valid valid info))
  val valid_prop = hoare_thm (Proof.context_of state) info |> Thm.term_of
  val state = prove (Binding.suffix_name "_valid" binding) after_qed valid_prop state
  in (info,state) end
\<close>

lemma semantics_seq: "semantics (p@q) m = 
  (\<Union>m'\<in>semantics p m. semantics q m')"
  sorry

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

lemma True
proof 

  define prog where "prog = [Set STR ''x'' 5, Guess STR ''y'', Add STR ''x'' STR ''y'']"

  do_prf \<open>fn state => let
    val (start_invariant,state) = Proof.map_context_result (add_invariant \<^binding>\<open>start\<close> \<^cterm>\<open>(\<lambda>m::mem. True)\<close>) state
    val (hoare,state) = add_hoare2 \<^binding>\<open>start\<close> test_prog (0,0) start_invariant start_invariant state
    val _ = \<^print> hoare
    in state end\<close>

    unfolding start_prog_def by simp

  (* Step 1: Set x 5 *)

  do_prf \<open>fn state => let
    val (post,state) = Proof.map_context_result (add_invariant \<^binding>\<open>step1\<close> \<^cterm>\<open>(postcondition_trivial (Set STR ''x'' 5) start_inv)\<close>) state
    val start = get_invariant (Proof.context_of state) "start" |> the
    val (hoare,state) = add_hoare2 \<^binding>\<open>step1\<close> test_prog (0,1) start post state
    in state end\<close>
    using step1_inv_def step1_prog_def by (rule valid)

  have step1_x5: "pc_imp step1_inv (\<lambda>m. m STR ''x'' = 5)"
    using step1_inv_def by (rule newvalue)

  (* Step 2: Guess y *)

  do_prf \<open>fn state => let
    val (post,state) = Proof.map_context_result (add_invariant \<^binding>\<open>step2\<close>
         \<^cterm>\<open>postcondition_pick (Guess STR ''y'') (-5) step1_inv\<close>) state
    val pre = get_invariant (Proof.context_of state) "step1" |> the
    val (hoare,state) = add_hoare2 \<^binding>\<open>step2\<close> test_prog (1,2) pre post state
    in state end\<close>
    using step2_inv_def step2_prog_def by (rule valid)

  have step2_x5: "pc_imp step2_inv (\<lambda>m. m STR ''x'' = 5)"
    using step2_inv_def apply (rule unchanged)
     apply (rule independent_ofI, simp)
    apply (tactic \<open>use_facts_tac \<^context> @{thms step1_x5} 1\<close>)
    by simp

  have step2_y5: "pc_imp step2_inv (\<lambda>m. m STR ''y'' = -5)"
    using step2_inv_def by (rule newvalue)

  have start_step2: "hoare start_inv (step1_prog @ step2_prog) step2_inv"
    using step1_valid step2_valid by (rule hoare_seq)    

  (* Step 3: Add x y *)

  do_prf \<open>fn state => let
    val (post,state) = Proof.map_context_result (add_invariant \<^binding>\<open>step3\<close>
       \<^cterm>\<open>(postcondition_trivial (Add STR ''x'' STR ''y'') step2_inv)\<close>) state
    val pre = get_invariant (Proof.context_of state) "step2" |> the
    val (hoare,state) = add_hoare2 \<^binding>\<open>step3\<close> test_prog (2,3) pre post state
    in state end\<close>
    using step3_inv_def step3_prog_def by (rule valid, simp)

  have step3_y5: "pc_imp step3_inv (\<lambda>m. m STR ''y'' = -5)"
    using step3_inv_def apply (rule unchanged)
      apply (rule independent_ofI, simp)
     apply simp
    apply (tactic \<open>use_facts_tac \<^context> @{thms step2_y5} 1\<close>)
    by simp

  have step3_x0: "pc_imp step3_inv (\<lambda>m. m STR ''x'' = 0)"
    using step3_inv_def apply (rule wp)
     apply simp
    apply (tactic \<open>use_facts_tac \<^context> @{thms step2_x5 step2_y5} 1\<close>)
    by simp

  have start_step3: "hoare start_inv prog step3_inv"
    using start_step2 step3_valid
    apply (rule hoare_seq')
    by (simp add: prog_def step1_prog_def step2_prog_def step3_prog_def)

  then have "hoare (\<lambda>_. True) prog (\<lambda>m. m STR ''x'' = 0)"
    apply (rule hoare_conseq')
    unfolding start_inv_def apply (simp add: pc_imp_def)
     apply (rule step3_x0)
    by simp

qed


end

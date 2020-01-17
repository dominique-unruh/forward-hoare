theory Forward_Hoare
  imports Main
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
| "postcondition1 (Add x y) Trivial I = Some (\<lambda>m. I (m(x:=m x - m y)))"
| "postcondition1 _ (Pick _) _ = None"

fun postcondition :: "program \<Rightarrow> pc_spec \<Rightarrow> invariant \<Rightarrow> invariant option" where
  "postcondition [] [] I = Some I"
| "postcondition (c#p) (s#ss) I = (case postcondition1 c s I of Some I' \<Rightarrow> postcondition p ss I' | None \<Rightarrow> None)"
| "postcondition _ _ _ = None"

ML \<open>
datatype pc_spec1 = Trivial | Pick of int
type pc_spec = pc_spec1 list
fun pc_spec1_to_term Trivial = \<^const>\<open>Trivial\<close>
  | pc_spec1_to_term (Pick i) = \<^const>\<open>Pick\<close> $ HOLogic.mk_number HOLogic.intT i
fun pc_spec_to_term pc = pc |> map pc_spec1_to_term |> HOLogic.mk_list \<^typ>\<open>pc_spec1\<close>
fun pc_spec_to_cterm ctxt pc = pc_spec_to_term pc |> Thm.cterm_of ctxt
\<close>

section \<open>Ranges\<close>

ML \<open>
type range = int * int
fun valid_range (program:program) ((start,endd):range) =
  start <= endd andalso start >= 0 andalso endd <= length program
(* Contract: valid_range = true *)
fun extract_range (program:program) ((start,endd):range) : program =
  program |> drop start |> take (endd-start)
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
  val (program_fragment_const,lthy) = 
      def' (bind "_prog") program_fragment_ct lthy
  val postcondition_ct = pc_spec_to_cterm lthy postcondition
  val (postcondition_const,lthy) = def' (bind "_pc") postcondition_ct lthy
  val invariant_ct = \<^const>\<open>postcondition\<close> 
        $ program_fragment_const
        $ postcondition_const
        $ precondition_const
    |> mk_the |> Thm.cterm_of lthy
  val (invariant_const,lthy) = def' (bind "_inv") invariant_ct lthy
  val spec : step_spec = {binding=binding, range=range, program_fragment=program_fragment, invariant_const=invariant_const,
    invariant_ct=invariant_ct, postcondition=postcondition, 
    postcondition_const=postcondition_const, postcondition_ct=postcondition_ct,
    program_fragment_const=program_fragment_const}
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

lemma True
proof 

  do \<open>make_step \<^binding>\<open>step1\<close> test_prog (0,1) (#invariant_const start_spec) [Trivial]\<close>
  have step1_exists: "postcondition step1_prog step1_pc start_inv = Some step1_inv"
    unfolding step1_inv_def step1_prog_def step1_pc_def by simp
  have step1_x5: "pc_imp step1_inv (\<lambda>m. m STR ''x'' = 5)"
    unfolding step1_inv_def pc_imp_def step1_prog_def step1_pc_def start_inv_def
    by simp

  do \<open>make_step \<^binding>\<open>step2\<close> test_prog (1,2) (#invariant_const (get_spec "step1" \<^context>)) [Pick ~5]\<close>
  have step2_x5: "pc_imp step2_inv (\<lambda>m. m STR ''x'' = 5)"
    using step1_x5
    unfolding step2_prog_def step2_pc_def pc_imp_def step2_inv_def
    by auto
  have step2_y5: "pc_imp step2_inv (\<lambda>m. m STR ''y'' = -5)"
    unfolding step2_inv_def step2_prog_def step2_pc_def pc_imp_def
    by simp
    
  do \<open>make_step \<^binding>\<open>step3\<close> test_prog (2,3) (#invariant_const (get_spec "step2" \<^context>)) [Trivial]\<close>
  have step3_y5: "pc_imp step3_inv (\<lambda>m. m STR ''y'' = -5)"
    unfolding step3_inv_def
    using step2_y5 unfolding step3_inv_def step3_prog_def step3_pc_def pc_imp_def
    by auto
  have step3_x0: "pc_imp step3_inv (\<lambda>m. m STR ''x'' = 0)"
    unfolding pc_imp_def step3_inv_def step3_prog_def step3_pc_def
  proof auto
    fix m
    assume s2: "step2_inv (m(STR ''x'' := m STR ''x'' - m STR ''y''))"
    show "m STR ''x'' = 0"
      using step2_x5[unfolded pc_imp_def, simplified, rule_format, OF s2]
      using step2_y5[unfolded pc_imp_def, simplified, rule_format, OF s2]
      by simp
  qed

qed


end

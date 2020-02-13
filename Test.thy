theory Test
  imports Demo_Hoare
begin

(* ML_file "test.ML" *)


lemma True
proof 

  program (demo_logic) prog: \<open>[Set STR ''x'' 5, Guess STR ''y'', Add STR ''x'' STR ''y'']\<close>

(*   do \<open>fn ctxt => let
    val prog = Demo_Hoare_Logic.ex_program [Set ("x", 5), Guess "y", Add ("x", "y")]
    val ctxt = add_program0 {binding=\<^binding>\<open>prog\<close>, logic="demo_logic", code=prog} ctxt
    in ctxt end\<close> *)

(* TODO: should be handled by program-command *)
  define prog where "prog = [Set STR ''x'' 5, Guess STR ''y'', Add STR ''x'' STR ''y'']"

  invariant (demo_logic) start: "\<lambda>m. True"

  (* Step 1: Set x 5 *)

  do_prf \<open>Forward_Hoare.new_hoare \<^binding>\<open>step1\<close> fst NONE (Demo_Hoare.ex_range (0,1)) "start"
     \<^term>\<open>(postcondition_trivial (Set STR ''x'' 5) start_inv)\<close>\<close>
    using step1_inv_def step1_prog_def by (rule valid)

  have step1_x5: "pc_imp step1_inv (\<lambda>m. m STR ''x'' = 5)"
    using step1_inv_def by (rule newvalue)

  (* Step 2: Guess y *)

  do_prf \<open>Forward_Hoare.new_hoare \<^binding>\<open>step2\<close> fst NONE (Demo_Hoare.ex_range (1,2)) "step1"
    \<^term>\<open>postcondition_pick (Guess STR ''y'') (-5) step1_inv\<close>\<close>
    using step2_inv_def step2_prog_def by (rule valid)

  have step2_x5: "pc_imp step2_inv (\<lambda>m. m STR ''x'' = 5)"
    using step2_inv_def apply (rule unchanged)
     apply (rule independent_ofI, simp)
    apply (tactic \<open>Demo_Hoare.use_facts_tac \<^context> @{thms step1_x5} 1\<close>)
    by simp

  have step2_y5: "pc_imp step2_inv (\<lambda>m. m STR ''y'' = -5)"
    using step2_inv_def by (rule newvalue)

  have start_step2: "hoare start_inv (step1_prog @ step2_prog) step2_inv"
    using step1_valid step2_valid by (rule hoare_seq)    

  (* Step 3: Add x y *)

  ML_val \<open>
    Forward_Hoare.Hoare_Data.get \<^context>
  \<close>

  do_prf \<open>Forward_Hoare.new_hoare \<^binding>\<open>step3\<close> fst NONE (Demo_Hoare.ex_range (2,3)) "step2"
    \<^term>\<open>(postcondition_trivial (Add STR ''x'' STR ''y'') step2_inv)\<close>\<close>
    using step3_inv_def step3_prog_def by (rule valid, simp)

  have step3_y5: "pc_imp step3_inv (\<lambda>m. m STR ''y'' = -5)"
    using step3_inv_def apply (rule unchanged)
      apply (rule independent_ofI, simp)
     apply simp
    apply (tactic \<open>Demo_Hoare.use_facts_tac \<^context> @{thms step2_y5} 1\<close>)
    by simp

  have step3_x0: "pc_imp step3_inv (\<lambda>m. m STR ''x'' = 0)"
    using step3_inv_def apply (rule wp)
     apply simp
    apply (tactic \<open>Demo_Hoare.use_facts_tac \<^context> @{thms step2_x5 step2_y5} 1\<close>)
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
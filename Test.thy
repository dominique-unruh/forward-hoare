theory Test
  imports Demo_Hoare
begin

ML_file "test.ML"

lemma True
proof 

  program (demo_logic) prog: \<open>[Set STR ''x'' 5, Guess STR ''y'', Add STR ''x'' STR ''y'']\<close>

  (* TODO: should be handled by program-command *)
  define prog where "prog = [Set STR ''x'' 5, Guess STR ''y'', Add STR ''x'' STR ''y'']"

  invariant (demo_logic) start: "\<lambda>m. True"

  (* Step 1: Set x 5 *)

  invariant (demo_logic) step1: \<open>(postcondition_trivial (Set STR ''x'' 5) start_inv)\<close>

  do_prf \<open>Forward_Hoare.new_hoare \<^binding>\<open>step1\<close> fst (Forward_Hoare.get_current_program \<^context> |> the)
          (Demo_Hoare.ex_range (0,1)) "start" "step1"\<close>
    using step1_inv_def by (rule valid)

  have step1_x5: "pc_imp step1_inv (\<lambda>m. m STR ''x'' = 5)"
    using step1_inv_def by (rule newvalue)

  (* Step 2: Guess y *)

  invariant (demo_logic) step2: \<open>postcondition_pick (Guess STR ''y'') (-5) step1_inv\<close>
  do_prf \<open>Forward_Hoare.extend_hoare \<^binding>\<open>step2\<close> "step1" #1 (Demo_Hoare.ex_range (1,2)) "step2"\<close>
    using step2_inv_def by (rule valid)

  have step2_x5: "pc_imp step2_inv (\<lambda>m. m STR ''x'' = 5)"
    using step2_inv_def apply (rule unchanged)
     apply (rule independent_ofI, simp)
    apply (tactic \<open>Demo_Hoare.use_facts_tac \<^context> @{thms step1_x5} 1\<close>)
    by simp

  have step2_y5: "pc_imp step2_inv (\<lambda>m. m STR ''y'' = -5)"
    using step2_inv_def by (rule newvalue)

  (* Step 3: Add x y *)

  invariant (demo_logic) step3: \<open>(postcondition_trivial (Add STR ''x'' STR ''y'') step2_inv)\<close>
  do_prf \<open>Forward_Hoare.extend_hoare \<^binding>\<open>step3\<close> "step2" #1 (Demo_Hoare.ex_range (2,3)) "step3"\<close>
    using step3_inv_def by (rule valid, simp)

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

  from step3_valid
  have "hoare (\<lambda>_. True) prog (\<lambda>m. m STR ''x'' = 0)"
    unfolding prog_def
    apply (rule hoare_conseq')
    unfolding start_inv_def apply (simp add: pc_imp_def)
     apply (rule step3_x0)
    by simp

qed

end

theory Test
  imports Demo_Hoare
begin

ML_file "test.ML"

program' (demo_logic) prog: \<open>[Set STR ''x'' 5, Guess STR ''y'', Add STR ''x'' STR ''y'']\<close>

(* TODO: should be handled by program-command *)
definition prog where "prog = [Set STR ''x'' 5, Guess STR ''y'', Add STR ''x'' STR ''y'']"

invariant' (demo_logic) start: "\<lambda>m. True"

lemma "hoare start_inv prog (\<lambda>m. m STR ''x'' = 0)"
proof  -

  (* Step 1: Set x 5 *)

  hoare step1: range 0-1 pre start post step1=trivial.

  invariant_has step1_x5: step1 \<rightarrow> "\<lambda>m. m STR ''x'' = 5"
    using step1_inv_def by (rule newvalue)

  (* Step 2: Guess y *)

  hoare step2: extends step1 range 1-2 post step2=pick -5.

  invariant_has step2_x5: step2 \<rightarrow> "\<lambda>m. m STR ''x'' = 5"

    using step2_inv_def apply (rule unchanged)
     apply (rule independent_ofI, simp)
    apply (tactic \<open>Demo_Hoare.use_facts_tac \<^context> @{thms step1_x5} 1\<close>)
    by simp

  invariant_has step2_y5: step2 \<rightarrow> "\<lambda>m. m STR ''y'' = -5"

    using step2_inv_def by (rule newvalue)

  (* Step 3: Add x y *)

  hoare step3: extends step2 range 2-3 post step3=trivial
    by auto

  invariant_has step3_y5: step3 \<rightarrow> "\<lambda>m. m STR ''y'' = -5"

    using step3_inv_def apply (rule unchanged)
      apply (rule independent_ofI, simp)
     apply simp
    apply (tactic \<open>Demo_Hoare.use_facts_tac \<^context> @{thms step2_y5} 1\<close>)
    by simp

  invariant_has step3_x0: step3 \<rightarrow> "\<lambda>m. m STR ''x'' = 0"

    using step3_inv_def apply (rule wp)
     apply simp
    apply (tactic \<open>Demo_Hoare.use_facts_tac \<^context> @{thms step2_x5 step2_y5} 1\<close>)
    by simp

  from step3_valid
  show ?thesis
    unfolding prog_def
    apply (rule hoare_conseq')
      apply (simp add: pc_imp_def)
     apply (rule step3_x0)
    by simp

qed

end

theory Test
  imports Demo_Hoare "HOL-Eisbach.Eisbach"
begin

ML_file "test.ML"

ML \<open>
open Forward_Hoare
\<close>

(* TODO: syntax highlighting does not work in program-term *)
Hoare program (demo_logic) prog: \<open>PROG[x := 5; y <- ?; x += y]\<close>

lemma "hoare (\<lambda>m. True) prog (\<lambda>m. m STR ''x'' = 0)"
  (is "hoare ?pre _ ?post")
proof  -

  invariant (demo_logic) start: ?pre

  (* Step 1: Set x 5 *)

  hoare step1: range 0-1 pre start post step1 = trivial

  hoare' invariant_has step1_x5: step1 \<rightarrow> "\<lambda>m. m STR ''x'' = 5"
    by updated

  (* Step 2: Guess y *)

  hoare step2: extends step1 range 1-2 post step2=pick -5

  from step1_x5
  hoare' invariant_has step2_x5: step2 \<rightarrow> "\<lambda>m. m STR ''x'' = 5"
    apply untouched by auto

  hoare' invariant_has step2_y5: step2 \<rightarrow> "\<lambda>m. m STR ''y'' = -5"
    by updated

  (* Step 3: Add x y *)

  hoare' step3: extends step2 range 2-3 post step3=trivial
    by auto

  from step2_y5
  hoare' invariant_has step3_y5: step3 \<rightarrow> "\<lambda>m. m STR ''y'' = -5"
    apply untouched by auto

  from step2_x5 step2_y5
  hoare' invariant_has step3_x0: step3 \<rightarrow> "\<lambda>m. m STR ''x'' = 0"
    apply wp by (auto simp: pc_imp_def)

  from step3_valid step3_x0
  show ?thesis
    by (auto intro: hoare_conseq' simp: start_inv_def prog_def)

qed

end

theory Test
  imports Demo_Hoare "HOL-Eisbach.Eisbach"
begin

named_theorems hoare_untouched
named_theorems hoare_updated
named_theorems hoare_wp

ML_file "test.ML"

ML \<open>
open Forward_Hoare
\<close>

declare unchanged[hoare_untouched]
declare newvalue[hoare_updated]
declare wp[hoare_wp]

program' (demo_logic) prog: \<open>[Set STR ''x'' 5, Guess STR ''y'', Add STR ''x'' STR ''y'']\<close>

(* TODO: should be handled by program-command *)
definition prog where "prog = [Set STR ''x'' 5, Guess STR ''y'', Add STR ''x'' STR ''y'']"

setup \<open>
  Attrib.setup \<^binding>\<open>current_invariant_def\<close> 
  (Scan.succeed (Thm.rule_attribute [] (fn context => fn thm =>
    case Context.proof_of context |> get_current_invariant_def of
      NONE => Drule.dummy_thm
    | SOME thm => thm)))
    "definition of the currently analyzed invariant (set by invariant_has)"
\<close>

method_setup untouched =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (invariant_untouched_tac ctxt))\<close> 
  "Invariant is preserved"

method_setup updated =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (invariant_updated_tac ctxt))\<close> 
  "Variable is update"

method_setup wp =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (invariant_wp_tac ctxt))\<close> 
  "Weakest precondition"

lemma "hoare (\<lambda>m. True) prog (\<lambda>m. m STR ''x'' = 0)"
  (is "hoare ?pre _ ?post")
proof  -

  invariant (demo_logic) start: ?pre

  (* Step 1: Set x 5 *)

  hoare step1: range 0-1 pre start post step1 = trivial.

  invariant_has step1_x5: step1 \<rightarrow> "\<lambda>m. m STR ''x'' = 5"
    by updated

  (* Step 2: Guess y *)

  hoare step2: extends step1 range 1-2 post step2=pick -5.

  invariant_has step2_x5: step2 \<rightarrow> "\<lambda>m. m STR ''x'' = 5"
    apply untouched
    using step1_x5 by (auto intro: independent_ofI)

  invariant_has step2_y5: step2 \<rightarrow> "\<lambda>m. m STR ''y'' = -5"
    by updated

  (* Step 3: Add x y *)

  hoare step3: extends step2 range 2-3 post step3=trivial
    by auto

  invariant_has step3_y5: step3 \<rightarrow> "\<lambda>m. m STR ''y'' = -5"
    apply untouched
    using step2_y5 by (auto intro: independent_ofI)

  invariant_has step3_x0: step3 \<rightarrow> "\<lambda>m. m STR ''x'' = 0"
    apply wp 
    using step2_x5 step2_y5 by (auto simp: pc_imp_def)

  from step3_valid step3_x0
  show ?thesis
    by (auto intro: hoare_conseq' simp: start_inv_def prog_def)

qed

end

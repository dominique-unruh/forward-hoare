theory Forward_Hoare
  imports Main
  keywords
        "hoare" :: prf_decl % "proof"
    and "hoare'" :: prf_goal % "proof"
    and "Hoare" :: thy_decl
    and "Hoare'" :: thy_goal

    and "range" "pre" "post" "extends" "program" "invariant_has" "config" "invariant"
begin

named_theorems hoare_untouched
(* Is this one meaningful? Or is wp basically the same? *)
named_theorems hoare_updated
named_theorems hoare_wp

definition SOLVE_WITH :: "String.literal \<Rightarrow> prop \<Rightarrow> prop" where "SOLVE_WITH _ == \<lambda>x. x"
lemma remove_SOLVE_WITH: "PROP P \<Longrightarrow> PROP SOLVE_WITH s PROP P"
  unfolding SOLVE_WITH_def by auto

ML_file "forward_hoare.ML"
ML_file "forward_hoare_utils.ML"
ML_file "hoare_logic.ML"


method_setup untouched =
  \<open>Scan.succeed (Forward_Hoare.invariant_untouched_method)\<close> 
  "Invariant is preserved"

method_setup updated =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (Forward_Hoare.invariant_updated_tac ctxt))\<close> 
  "Variable is updated"

method_setup wp =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (Forward_Hoare.invariant_wp_tac ctxt))\<close> 
  "Weakest precondition"

syntax "_invariant_implication" :: "id \<Rightarrow> 'a \<Rightarrow> bool" ("{_ \<Rightarrow> _}")
parse_translation \<open>[
  (\<^syntax_const>\<open>_invariant_implication\<close>, Forward_Hoare.invariant_implication_tr)]\<close>


end

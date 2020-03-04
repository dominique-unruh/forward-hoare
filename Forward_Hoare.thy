theory Forward_Hoare
  imports Pure
    keywords
 "invariant" :: prf_decl % "proof"
    and "invariant'" :: thy_decl

    and "hoare" :: prf_decl % "proof"
    and "hoare'" :: prf_goal % "proof"
    and "Hoare" :: thy_decl
    and "Hoare'" :: thy_goal

    and "range" "pre" "post" "extends" "program" "invariant_has"
begin

named_theorems hoare_untouched
(* Is this one meaningful? Or is wp basically the same? *)
named_theorems hoare_updated
named_theorems hoare_wp

ML_file "forward_hoare.ML"
ML_file "hoare_logic.ML"


method_setup untouched =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (Forward_Hoare.invariant_untouched_tac ctxt))\<close> 
  "Invariant is preserved"

method_setup updated =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (Forward_Hoare.invariant_updated_tac ctxt))\<close> 
  "Variable is update"

method_setup wp =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (Forward_Hoare.invariant_wp_tac ctxt))\<close> 
  "Weakest precondition"


end

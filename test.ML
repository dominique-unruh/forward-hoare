local
open Forward_Hoare
in

fun current_invariant_tac thms ctxt = let
  val thms = thms ctxt
  val inv_def = get_the_current_invariant_def ctxt
  in
    resolve_tac ctxt thms
    THEN'
    solve_tac ctxt [inv_def]
  end

val invariant_untouched_tac = current_invariant_tac (fn ctxt => Named_Theorems.get ctxt \<^named_theorems>\<open>hoare_untouched\<close>)
val invariant_updated_tac = current_invariant_tac (fn ctxt => Named_Theorems.get ctxt \<^named_theorems>\<open>hoare_updated\<close>)
val invariant_wp_tac = current_invariant_tac (fn ctxt => Named_Theorems.get ctxt \<^named_theorems>\<open>hoare_wp\<close>)

end
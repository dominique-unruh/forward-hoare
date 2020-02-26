local
open Forward_Hoare
in

fun postcondition_trivial _ program_fragment pre = let
  val instruction = case HOLogic.dest_list program_fragment of
    [i] => i | _ => error "Program must be one instruction long"
  val post = \<^const>\<open>postcondition_trivial\<close> $ instruction $ pre
  fun tac ctxt = resolve_tac ctxt @{thms valid[OF reflexive]} 1
  in
    (post, tac)
  end

end
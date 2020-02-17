local
open Forward_Hoare
in

val _ = Raw_Simplifier.rewrite

fun join_hoare binding (hoare1:string) (hoare2:string) state = let
  val ctxt = Proof.context_of state
  val hoare1' = Forward_Hoare.get_hoare ctxt hoare1 |> the
  val hoare2' = Forward_Hoare.get_hoare ctxt hoare2 |> the
  val program = #program hoare1'
  val _ = if #program hoare1' <> #program hoare2' then error "mismatch" else ()
  val _ = if #postcondition hoare1' <> #precondition hoare2' then error "mismatch" else ()
  val program' = program |> Forward_Hoare.get_program ctxt |> the
  val logic = program' |> #logic |> Forward_Hoare.get_logic' ctxt |> the
  val a = hoare1' |> #precondition |> Forward_Hoare.get_invariant ctxt |> the |> #const
  val b = hoare1' |> #postcondition |> Forward_Hoare.get_invariant ctxt |> the |> #const
  val c = hoare2' |> #postcondition |> Forward_Hoare.get_invariant ctxt |> the |> #const
(* TODO give validity thms with unfolded program definitions *)
  val (range,joined_thm) = #join_hoare logic ctxt (#code program') a (#range hoare1') b (#range hoare2') c
          (#valid hoare1') (#valid hoare2')
  val program_fragment = (#extract_range logic) (#code program') range
  val (program_fragment_const,state) = 
      def'' (Binding.suffix_name "_prog" binding) program_fragment state
(* TODO: bind joined_thm *)

  val state = Proof.map_context (snd o Local_Theory.note ((Binding.suffix_name "_valid" binding, []), [joined_thm])) state

  val info : hoare = {binding=binding, range=range,
    precondition= #precondition hoare1',
    postcondition= #postcondition hoare2',
    program_fragment_const=program_fragment_const,
    program=program,
    valid=joined_thm
  }
  
  val state = Proof.map_context (add_hoare0 info) state

  in (state,info) end

fun extend_hoare binding (previous:string) after_qed0 range (postcondition:string) state = let
  val ctxt = Proof.context_of state
  val binding_step = Binding.suffix_name "_step" binding
  val previous_hoare = Forward_Hoare.get_hoare ctxt previous |> the
  val program = #program previous_hoare
  val precondition = #postcondition previous_hoare
  fun after_qed (state, hoare) = let
    val (state, joined_hoare) = join_hoare binding previous (Binding.name_of binding_step) state
    in after_qed0 (state, hoare, joined_hoare) end
  val state = Forward_Hoare.new_hoare binding_step after_qed program range precondition postcondition state
in state end

end
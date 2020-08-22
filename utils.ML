structure Utils = struct

type 'a toolkit = {
  define: binding -> binding -> term -> 'a -> (term*thm*'a),
  declaration: declaration -> 'a -> 'a,
  context: 'a -> Context.generic,
  theorem: (thm -> 'a -> 'a) -> term -> 'a -> Proof.state,
  note: binding -> thm -> 'a -> 'a,
  qed: Proof.state -> 'a
}

val lthy_toolkit : local_theory toolkit = let

  fun define bind thm_bind prop lthy =
    case Local_Theory.define ((bind,NoSyn),((thm_bind,[]),prop)) lthy of
      ((const,(_,thm)),lthy) => (const,thm,lthy)
  val declaration = Local_Theory.declaration {syntax=false, pervasive=false}
  val context = Context.Proof
  fun theorem after_qed prop lthy = let
    fun after_qed' [[thm]] lthy = after_qed thm lthy
      | after_qed' _ _ = raise Match
    in Proof.theorem NONE after_qed' [[(prop, [])]] lthy end
  fun note bind thm lthy = Local_Theory.note ((bind,[]),[thm]) lthy |> snd
  val qed = Proof.global_done_proof
  in { define=define, declaration=declaration, context=context, theorem=theorem, note=note, qed=qed } end

val proof_toolkit : Proof.state toolkit = let

  fun define bind thm_bind prop state = 
    case Proof.map_context_result (Local_Defs.define [((bind,NoSyn),((thm_bind,[]),prop))]) state
      of ([(const,(_,thm))],state) => (const,thm,state)
       | _ => raise Match

  fun declaration decl = decl Morphism.identity |> Context.proof_map |> Proof.map_context
  val context = Proof.context_of #> Context.Proof
  fun theorem after_qed prop state = let
    fun after_qed' (_,[[thm]]) state = after_qed thm state
      | after_qed' _ _ = raise Match
    in Proof.have false NONE after_qed' [] [] 
       [((Binding.empty,[]),[(prop,[])])] true state |> snd end

  fun note bind thm state = 
    Proof.map_context_result (Proof_Context.note_thmss "" [((bind,[]),[([thm],[])])]) state |> snd

  val qed = Proof.local_done_proof

  in { define=define, declaration=declaration, context=context, theorem=theorem, note=note, qed=qed } end

(* Given a sequence of results (e.g., possible result of a method application),
   filters out the errors in that sequence. If there are no successful results,
   raises an error (default_msg, possibly prefixing the first error in the sequence, if any) *)
fun ensure_result default_msg (seq:'a Seq.result Seq.seq) : 'a Seq.seq =
  let
    fun result opt_msg xq =
      (case (opt_msg, Seq.pull xq) of
        (_, SOME (Seq.Result x, xq)) => Seq.cons x (Seq.filter_results xq)
      | (SOME _, SOME (Seq.Error _, xq')) => result opt_msg xq'
      | (NONE, SOME (Seq.Error msg, xq')) => result (SOME msg) xq'
      | (SOME msg, NONE) => error (default_msg() ^ ": " ^ msg ())
      | (NONE, NONE) => error (default_msg()))
  in result NONE seq end


end
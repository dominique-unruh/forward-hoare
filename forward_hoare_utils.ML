structure Forward_Hoare_Utils = struct

(* ctxt - context for parsing pattern (can be \<^context>)
   which_goal - which new subgoal of tac goal should be guarded (e.g., 1 for first subgoal)
   pattern - pattern that the new subgoal should *not* match
   tac - tactic that should be guarded ('tac ctxt i' must work on i-th subgoal) *)
fun no_match_tactic ctxt which_goal pattern tac = let
  val pattern' = Syntax.read_prop (ctxt |> Proof_Context.set_mode Proof_Context.mode_pattern) pattern
  in fn ctxt => fn i => let 
      val match_tac = SUBGOAL (fn (t,_) => let
          val matches = (Pattern.match (Proof_Context.theory_of ctxt) 
                          (pattern', Logic.strip_assums_concl t) (Vartab.empty,Vartab.empty);
                       true) handle Pattern.MATCH => false
          in if matches then no_tac else all_tac end) (i+which_goal-1)
      in tac ctxt i THEN match_tac end
  end
end

functor Forward_Hoare_Utils() = struct

local
open Forward_Hoare
in

val this_logic_reference: Forward_Hoare.logic option Unsynchronized.ref = Unsynchronized.ref NONE

fun this_logic () : Forward_Hoare.logic =
  !this_logic_reference |> the' (fn _ => "INTERNAL ERROR: this_logic_reference undefined")

(* Default implementation *)
type options = {last_program: string option}
fun set_last_program name (_:options) = {last_program = SOME name}
(* Default implementation *)
val default_options = {last_program = NONE}
(* Default implementation *)
fun set_option "@last_program" name _ _ = set_last_program name
  | set_option name _ _ _ = error ("Unknown option " ^ name ^ " for logic " ^ name_of_logic (this_logic()))

fun get_current_program_name ({last_program}:options) = last_program |> the' (fn _ => "No current program defined")

(* name is an internal (fully qualified) program name *)
fun get_my_program ctxt name = let
  val context = Context.Proof ctxt
  val prog : program = get_the_program_internal context name
  val _ = if #logic prog = name_of_logic (this_logic()) then ()
          else error (program_name_extern ctxt name ^ " is from logic " ^ #logic prog ^ " but needed a program from logic " ^ name_of_logic (this_logic()))
  in #code prog end

(* Default implementation *)
fun invariant_parse_translation _ _ t = t

(* Default implementation *)
val subgoal_tactics: (string * (Proof.context -> int -> tactic)) list = []

(* Default implementation *)
fun invariant_consequences _ _ = []

end
end
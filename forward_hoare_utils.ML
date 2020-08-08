functor Forward_Hoare_Utils(Name: sig val logic_name : string end) = struct

local
open Forward_Hoare
in

(* TODO make lazy val *)
fun this_logic ctxt : Forward_Hoare.logic =
  Forward_Hoare.get_the_logic ctxt Name.logic_name

type options = {last_program: string option}
fun set_last_program name (_:options) = {last_program = SOME name}

val default_options = {last_program = NONE}
fun set_option "@last_program" name _ _ = set_last_program name
  | set_option name _ _ _ = error ("Unknown option " ^ name ^ " for logic " ^ Name.logic_name)

fun get_current_program_name ({last_program}:options) = last_program |> the' (fn _ => "No current program defined")

fun get_my_program ctxt name = let
  val context = Context.Proof ctxt
  val prog : program = get_the_program context name
  val _ = if #logic prog = Name.logic_name then ()
          else error (Binding.print (#binding prog) ^ " is from logic " ^ #logic prog ^ " but needed a program from logic " ^ Name.logic_name)
  in #code prog end

end
end
structure Demo_Hoare = struct

open Forward_Hoare

datatype instruction = Add of var*var | Set of var*int | Guess of var
  fun instruction_to_term (Set (x, i)) = \<^const>\<open>Set\<close> $ HOLogic.mk_literal x $ HOLogic.mk_number HOLogic.intT i
    | instruction_to_term (Guess x) = \<^const>\<open>Guess\<close> $ HOLogic.mk_literal x
    | instruction_to_term (Add (x,y)) = \<^const>\<open>Add\<close> $ HOLogic.mk_literal x $ HOLogic.mk_literal y
  fun program_to_term p = map instruction_to_term p |> HOLogic.mk_list \<^typ>\<open>instruction\<close>
  fun term_to_instruction (Const (\<^const_name>\<open>Set\<close>,_) $ x $ n) =
            Set (HOLogic.dest_literal x, snd (HOLogic.dest_number n))
    | term_to_instruction (Const (\<^const_name>\<open>Guess\<close>,_) $ x) =
            Guess (HOLogic.dest_literal x)
    | term_to_instruction (Const (\<^const_name>\<open>Add\<close>,_) $ x $ y) =
            Add (HOLogic.dest_literal x, HOLogic.dest_literal y)
    | term_to_instruction t = raise TERM("term_to_instruction",[t])
  fun term_to_program t = HOLogic.dest_list t |> map term_to_instruction

structure Demo_Hoare_Logic = Hoare_Logic(
  type program = instruction list
  type range = int * int

  val binding = \<^binding>\<open>demo_logic\<close>

  fun read_program ctxt str = let
    val t = Syntax.read_term ctxt str
    val p = term_to_program t
  in p end
    
  fun read_range ctxt str = error "read_range"

  fun hoare_thm ctxt pre prog post = \<^const>\<open>hoare\<close> $ pre $ prog $ post |> HOLogic.mk_Trueprop

  fun valid_range (program:program) ((start,endd):range) =
    start <= endd andalso start >= 0 andalso endd <= length program

  fun extract_range (program:program) ((start,endd):range) : term =
    program |> drop start |> take (endd-start) |> program_to_term

  fun read_invariant ctxt str = Syntax.read_term ctxt ("(" ^ str ^ ") :: Demo_Hoare.mem \<Rightarrow> HOL.bool")
)

val ex_range = Demo_Hoare_Logic.ex_range
val range_ex = Demo_Hoare_Logic.range_ex
val ex_program = Demo_Hoare_Logic.ex_program
val program_ex = Demo_Hoare_Logic.program_ex

fun use_facts_tac ctxt thms = 
  EVERY' (map (fn thm => forward_tac ctxt [thm COMP @{thm pc_impD}]) (rev (tl thms)))
  THEN' (dresolve_tac ctxt [hd thms COMP @{thm pc_impD}])


end
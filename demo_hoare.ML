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
    
  (* TODO support relative ranges *)
  fun read_range _ : range context_parser = 
    Scan.lift (Parse.nat --| Parse.minus -- Parse.nat)

  fun pretty_range _ (start,stop) = Pretty.strs [string_of_int start,"-",string_of_int stop]

  fun hoare_thm _ pre prog post = \<^const>\<open>hoare\<close> $ pre $ prog $ post |> HOLogic.mk_Trueprop

  fun valid_range (program:program) ((start,endd):range) =
    start <= endd andalso start >= 0 andalso endd <= length program

  fun extract_range (program:program) ((start,endd):range) : term =
    program |> drop start |> take (endd-start) |> program_to_term

  fun read_invariant ctxt str = Syntax.read_term ctxt ("(" ^ str ^ ") :: Demo_Hoare.mem \<Rightarrow> HOL.bool")

  val join_hoare_goal = 
    \<^const>\<open>hoare\<close> $ Var(("pre",0), \<^typ>\<open>invariant\<close>) $ Var(("prog",0), \<^typ>\<open>program\<close>) $ Var(("post",0), \<^typ>\<open>invariant\<close>)
    |> HOLogic.mk_Trueprop |> Thm.cterm_of \<^context> |> Goal.init
    |> SINGLE (resolve_tac \<^context> @{thms hoare_seq'} 1) |> the
    |> \<^print>

  fun join_hoare ctxt _ _ (l1,l2) _ (l3,l4) _ h1 h2 = let
    val _ = if l2 <> l3 then error "mismatch" else ()
    val thm = join_hoare_goal 
              |> SINGLE (solve_tac ctxt [h1] 1
                    THEN solve_tac ctxt [h2] 1
                    THEN REPEAT (resolve_tac ctxt @{thms append_aux1} 1)
                    THEN solve_tac ctxt @{thms append_aux2} 1) |> the
              |> Goal.finish ctxt
    val r = (l1,l4)
    in (r,thm) end
)

val ex_range = Demo_Hoare_Logic.ex_range
val range_ex = Demo_Hoare_Logic.range_ex
val ex_program = Demo_Hoare_Logic.ex_program
val program_ex = Demo_Hoare_Logic.program_ex
val logic = Demo_Hoare_Logic.logic

fun use_facts_tac ctxt thms = 
  EVERY' (map (fn thm => forward_tac ctxt [thm COMP @{thm pc_impD}]) (rev (tl thms)))
  THEN' (dresolve_tac ctxt [hd thms COMP @{thm pc_impD}])


end
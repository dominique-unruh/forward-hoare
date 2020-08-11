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

fun independence_tac ctxt = 
  (resolve_tac ctxt @{thms independent_ofI filter_literal_neq} THEN' SOLVED' (asm_simp_tac ctxt))

structure Demo_Hoare_Logic = Hoare_Logic(
  val binding = \<^binding>\<open>demo_logic\<close>
  structure Utils = Forward_Hoare_Utils()
  open Utils

  (* type program = instruction list *)
  type range = string * int * int

(*   type options = unit
  val default_options = ()
  fun set_option _ _ _ _ _ = error "Logic demo_logic does not have any options" *)

  fun program_term_typ _ = \<^typ>\<open>program\<close>

(*   fun read_program ctxt str = let
    val t = Syntax.read_term ctxt str
    val p = term_to_program t
  in p end *)
    
  (* TODO support relative ranges *)
  fun read_range options _ : range context_parser = 
    Scan.lift (Parse.nat --| Parse.minus -- Parse.nat)
      >> (fn (start,endd) => (get_current_program_name options, start, endd))

  fun pretty_range _ (_,start,stop) = Pretty.strs [string_of_int start,"-",string_of_int stop]

  fun hoare_thm _ pre prog post = \<^const>\<open>hoare\<close> $ pre $ prog $ post |> HOLogic.mk_Trueprop

(*   fun valid_range (program:term) ((start,endd):range) =
    start <= endd andalso start >= 0 andalso endd <= length (HOLogic.dest_list program) *)

  fun invariant_implication _ (t1:term) (t2:term) = 
    \<^const>\<open>pc_imp\<close> $ t1 $ t2

  fun invariant_implication_lhs (Const(\<^const_name>\<open>pc_imp\<close>,_) $ t1 $ _) = t1

  fun extract_range ctxt ((program,start,endd):range) : term =
    get_my_program ctxt program |> HOLogic.dest_list |> drop start |> take (endd-start) |> HOLogic.mk_list \<^typ>\<open>instruction\<close>

  fun check_program ctxt program = let
    val list = HOLogic.dest_list program
               handle TERM _ => error "Invalid program: should be a list of instructions"
    val _ = List.app (fn t => (term_to_instruction t 
            handle TERM _ => error ("Invalid instruction: " ^ Syntax.string_of_term ctxt t); ())) list
    val _ = term_to_program program
    in () end

  (* fun read_invariant ctxt str = read_term_typed ctxt \<^typ>\<open>invariant\<close> str *)

  fun invariant_typ _ = \<^typ>\<open>invariant\<close>
  fun check_invariant _ _ = ()

  fun postcondition_trivial program_fragment pre = let
    val instruction = case HOLogic.dest_list program_fragment of
      [i] => i | _ => error "Program must be one instruction long"
    val post = \<^const>\<open>postcondition_trivial\<close> $ instruction $ pre
    fun tac ctxt = resolve_tac ctxt @{thms valid[OF reflexive]} 1
    in
      (post, tac)
    end

  fun postcondition_pick i program_fragment pre = let
    val instruction = case HOLogic.dest_list program_fragment of
      [i] => i | _ => error "Program must be one instruction long"
    val post = \<^const>\<open>postcondition_pick\<close> $ instruction $ HOLogic.mk_number \<^typ>\<open>int\<close> i $ pre
    fun tac ctxt = resolve_tac ctxt @{thms valid[OF reflexive]} 1
    in
      (post, tac)
    end
  
  (* fun program_morphism _ prog = prog *)

  val postcondition_generators = Symtab.make [
    ("trivial", Scan.succeed postcondition_trivial |> Scan.lift),
    ("pick", Scan.lift Parse.int >> postcondition_pick)
  ]

  val join_hoare_goal = 
    \<^const>\<open>hoare\<close> $ Var(("pre",0), \<^typ>\<open>invariant\<close>) $ Var(("prog",0), \<^typ>\<open>program\<close>) $ Var(("post",0), \<^typ>\<open>invariant\<close>)
    |> HOLogic.mk_Trueprop |> Thm.cterm_of \<^context> |> Goal.init
    |> SINGLE (resolve_tac \<^context> @{thms hoare_seq'} 1) |> the

  fun join_hoare ctxt _ ((prog12,l1,l2):range) _ ((prog34,l3,l4):range) _ h1 h2 = let
    val _ = if l2 <> l3 then error "mismatch" else ()
    val _ = if prog12 <> prog34 then error "mismatch" else ()
    val thm = join_hoare_goal 
              |> SINGLE (solve_tac ctxt [h1] 1
                    THEN solve_tac ctxt [h2] 1
                    THEN REPEAT (resolve_tac ctxt @{thms append_aux1} 1)
                    THEN solve_tac ctxt @{thms append_aux2} 1) |> the
              |> Goal.finish ctxt
    val r = (prog12,l1,l4)
    in (r,thm) end

 val subgoal_tactics = [("independence_tac",independence_tac)]

)

val ex_range = Demo_Hoare_Logic.ex_range
val range_ex = Demo_Hoare_Logic.range_ex
(* val ex_program = Demo_Hoare_Logic.ex_program *)
(* val program_ex = Demo_Hoare_Logic.program_ex *)
val logic = Demo_Hoare_Logic.logic

fun use_facts_tac ctxt thms = 
  EVERY' (map (fn thm => forward_tac ctxt [thm COMP @{thm pc_impD}]) (rev (tl thms)))
  THEN' (dresolve_tac ctxt [hd thms COMP @{thm pc_impD}])

end

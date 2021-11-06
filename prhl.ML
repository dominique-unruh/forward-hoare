structure PRHL =
struct

(* TODO

   Uniform syntax for selecting logic (right after "hoare" keyword)

   Options can be given locally (e.g., when defining a program)?

   Use invariant syntax translation when declaring invariants

   Name space support for invariants, logics, hoare judgments

*)

open Forward_Hoare
open Utils

fun infer ctxt ts = 
  Drule.infer_instantiate' ctxt (ts |> map (Thm.cterm_of ctxt #> SOME))

fun is_prod (Type(\<^type_name>\<open>prod\<close>,_)) = true
  | is_prod _ = false

fun dest_listT (Type(\<^type_name>\<open>list\<close>, [T])) = T
  | dest_listT T = raise TYPE("dest_listT", [T], [])

fun instructionT T = Type(\<^type_name>\<open>instruction\<close>, [T])
fun dest_instructionT (Type(\<^type_name>\<open>instruction\<close>, [T])) = T
  | dest_instructionT T = raise TYPE("dest_instructionT", [T], [])
  
fun programT T = instructionT T |> HOLogic.listT
fun program2T T1 T2 = HOLogic.mk_prodT (programT T1, programT T2)
fun dest_programT T = dest_listT T |> dest_instructionT
fun exprT T T' = T --> T'
fun dest_exprT _ (Type(\<^type_name>\<open>fun\<close>,[T,T'])) = (T,T')
  | dest_exprT caller T = raise TYPE(caller^": dest_exprT", [T], [])
fun invariantT T = T --> HOLogic.boolT
fun invariant2T T1 T2 = T1 --> T2 --> HOLogic.boolT
fun is_rinvT (Type(\<^type_name>\<open>fun\<close>, [_, (Type(\<^type_name>\<open>fun\<close>, [_, \<^typ>\<open>bool\<close>]))])) = true
  | is_rinvT _ = false
fun dest_invariantT _ (Type(\<^type_name>\<open>fun\<close>, [T, \<^typ>\<open>bool\<close>])) = T
  | dest_invariantT caller T = raise TYPE(caller^": dest_invariantT", [T], [])
fun dest_invariant2T _ (Type(\<^type_name>\<open>fun\<close>, [T, (Type(\<^type_name>\<open>fun\<close>, [T', \<^typ>\<open>bool\<close>]))])) = (T,T')
  | dest_invariant2T caller T = raise TYPE(caller^": dest_invariant2T", [T], [])

fun varT T T' = Type(\<^type_name>\<open>var\<close>, [T,T'])
fun dest_varT _ (Type(\<^type_name>\<open>var\<close>, [T,T'])) = (T,T')
  | dest_varT caller T = raise TYPE(caller^": dest_varT", [T], [])

fun spmfT T = Type(\<^type_name>\<open>pmf\<close>, [Type(\<^type_name>\<open>option\<close>, [T])])

fun append_conv ct = 
  (Conv.rewr_conv @{thm append_conv0}
  else_conv
  (Conv.rewr_conv @{thm append_conv1}
   then_conv (Conv.arg_conv append_conv)))
  ct

fun is_unique_sorted [] = true
  | is_unique_sorted [_] = true
  | is_unique_sorted (x::(ys as y::_)) = x < y andalso is_unique_sorted ys


fun literal_neq_tac ctxt = SUBGOAL (fn (t,i) => let
  (* Checking that we have an inequality of literals *)
  val _ = t |> HOLogic.dest_Trueprop |> HOLogic.dest_not |> HOLogic.dest_eq
          |> apply2 HOLogic.dest_literal
          handle TERM _ => raise TERM ("literal_neq_tac: not an inequality of literals", [t])
  in simp_tac ctxt i end)

fun indep_tac ctxt = let
  val rules = Named_Theorems.get ctxt \<^named_theorems>\<open>independence\<close>
  val fail_tac = SUBGOAL (fn (t,_) => let
      val error1 = "Could not show independence. Unsolved goal: " ^ Syntax.string_of_term ctxt t
      val error2 = "\nProve a suitable rule for it and declare attribute [independence]"
      in error (error1 ^ error2) end)
  fun tac i = ((resolve_tac ctxt rules THEN_ALL_NEW tac) ORELSE' fail_tac) i
  in tac end
  
(* fun indep_tac ctxt = SUBGOAL (fn (t,i) => let
  val (body,v,T) = case t of \<^const>\<open>Trueprop\<close> $ (Const(\<^const_name>\<open>independent_of\<close>,_) $
                              Abs(_,T,body) $ v) => (body,v,T)
                         | _ => raise TERM("indep_tac: wrong shape", [t])
  (* val _ = body |> Syntax.string_of_term ctxt |> writeln *)
  in case body of
    Bound 0 $ _ => resolve_tac ctxt @{thms independent_of_var} i
      THEN literal_neq_tac ctxt i
  | t1 $ t2 => let
      val rule = infer ctxt [Abs("mem",T,t1), v, Abs("mem",T,t2)] @{thm independent_of_split}
    val tac = resolve_tac ctxt [rule]
      in (tac THEN_ALL_NEW indep_tac ctxt) i end
  | Abs _ => raise TERM("indep_tac: unsupported", [body])
  | Bound _ => raise TERM("indep_tac: unsupported", [body])
  | _ => solve_tac ctxt @{thms independent_of_const} i
  end
  ) *)


datatype rangestep = 
  Line of int 
  | If of int * bool * rangestep list

datatype instruction = 
  BasicInstruction of term
  | IfThenElse of term * instruction list * instruction list
  | Block of instruction list (* A block that is not represented in the final term, for internal purposes only *)

type range1 = rangestep list
type range1p = string * range1

fun linenum_of_rangestep (Line n) = n
  | linenum_of_rangestep (If (n,_,_)) = n

fun isSortedStep (Line _) = true
  | isSortedStep (If (_,_,range)) = isSorted1 range

and isSorted1 ([]:range1) = true
  | isSorted1 ([step]) = isSortedStep step
  | isSorted1 (step1::step2::range) = 
      linenum_of_rangestep step1 < linenum_of_rangestep step2
      andalso isSorted1 (step2::range)

fun shift_range1 (Line n :: range) = Line (n+1) :: shift_range1 range
  | shift_range1 (If (n,x,y) :: range) = If (n+1,x,y) :: shift_range1 range
  | shift_range1 [] = []

fun unshift_range1 (Line n :: range) = Line (n-1) :: unshift_range1 range
  | unshift_range1 (If (n,x,y) :: range) = If (n-1,x,y) :: unshift_range1 range
  | unshift_range1 [] = []

fun term_to_instruction (Const(\<^const_name>\<open>IfThenElse\<close>,_) $ e $ p1 $ p2) =
      IfThenElse (e, term_to_program p1, term_to_program p2)
  | term_to_instruction (Const(\<^const_name>\<open>Block\<close>,_) $ p) =
      Block (term_to_program p)
  | term_to_instruction t =
      BasicInstruction t

and term_to_program prog = 
  prog |> HOLogic.dest_list |> map term_to_instruction

(* makes sure there are no Block's at toplevel *)
fun flatten_blocks (Block p :: q) = flatten_blocks p @ flatten_blocks q
  | flatten_blocks (i :: p) = i :: flatten_blocks p
  | flatten_blocks [] = []

(* instruction_to_term (term_to_instruction t) = t for well-typed t *)
fun instruction_to_term _ (BasicInstruction t) = t
  | instruction_to_term memT (IfThenElse (e, p1, p2)) = let
    val eT = exprT memT HOLogic.boolT
    val p1' = program_to_term memT p1
    val p2' = program_to_term memT p2
    val iT = instructionT memT
    val pT = HOLogic.listT iT
    in Const(\<^const_name>\<open>IfThenElse\<close>, eT --> pT --> pT --> iT) $ e $ p1' $ p2' end
  | instruction_to_term memT (Block p) =
    Const(\<^const_name>\<open>Block\<close>, programT memT --> instructionT memT) $ 
      program_to_term memT p

and program_to_term memT prog =
  prog |> map (instruction_to_term memT) |> HOLogic.mk_list (instructionT memT)

fun extract_if_side _ (Const(\<^const_name>\<open>IfThenElse\<close>,_) $ e $ thenProg $ elseProg) side = let
  val memT = fastype_of e |> Term.domain_type
  val e' = if side then e else Abs("mem", memT, \<^const>\<open>Not\<close> $ (e $ Bound 0))
  val assert = Const(\<^const_name>\<open>Assert\<close>, (memT --> HOLogic.boolT) --> instructionT memT)
                $ e'
  val sideprog = if side then thenProg else elseProg
  val result = HOLogic.cons_const (instructionT memT) $ assert $ sideprog
  in result end
  | extract_if_side ctxt t _ =
    error ("Expected an if-statement but got " ^ Syntax.string_of_term ctxt t)

fun if_side_assert side e = let
  val memT = e |> fastype_of |> dest_exprT "if_side_assert" |> fst
  val e' = if side then e else Abs("mem", memT, \<^const>\<open>Not\<close> $ (e $ Bound 0))
  val assert = Const(\<^const_name>\<open>Assert\<close>, (memT --> HOLogic.boolT) --> instructionT memT) $ e'
        |> BasicInstruction
  in assert end


fun extract_rangestep _ _ (prog:instruction list) (Line i) = (nth prog (i-1)
        handle Subscript => error ("No " ^ string_of_int i ^ ". statement (only " ^ string_of_int (length prog) ^ " statements)"))
  | extract_rangestep ctxt memT prog (If (i,side,range)) = let
      val (IfThenElse (e, p1, p2)) = nth prog (i-1)
      val p = if side then p1 else p2
(*       val e' = if side then e else Abs("mem", memT, \<^const>\<open>Not\<close> $ (e $ Bound 0))
      val assert = Const(\<^const_name>\<open>Assert\<close>, (memT --> HOLogic.boolT) --> instructionT memT) $ e'
            |> BasicInstruction *)
      val assert = if_side_assert side e
    in extract_range1 ctxt memT (assert::p) (shift_range1 range) |> Block end
    
and extract_range1 ctxt memT prog range1 : instruction list =
  map (extract_rangestep ctxt memT prog) range1


(* Proves "instructions_commute a b" if possible  *)
fun swap_instructions ctxt (a:term) (b:term) : thm = let
  val T = fastype_of a
  val prop = Const(\<^const_name>\<open>instructions_commute\<close>, T --> T --> HOLogic.boolT) $ a $ b |> HOLogic.mk_Trueprop
  fun tac ctxt = (resolve_tac ctxt @{thms commute_indep_Sample_Sample
commute_indep_Sample_Set commute_indep_Set_Sample commute_indep_Set_Set 
commute_indep_Assert_Set commute_indep_BlockSet_Set commute_indep_BlockAssert_Set
} 
      THEN_ALL_NEW indep_tac ctxt) 1
  val thm = Goal.prove ctxt [] [] prop (fn {context=ctxt,...} => tac ctxt)
  in thm end

(* insert_sorted_into_sorted ctxt (pos:rangestep, instr:instruction) (range:range1,prog:instruction list)

  Inserts instr into prog, where instr is at position post, and prog is extracted using range.
  (If possible.)
  Assumes that range and pos are sorted.

  Returns:
    range': range of the returned program
    prog': prog with instr inserted
    thm: semantics (instr#prog) = semantics (prog')

 *)
fun insert_sorted_into_sorted ctxt memT (pos,i) ([],[]) : range1 * instruction list * thm = let
      val thm = infer ctxt [instruction_to_term memT i] @{thm insert_into_ordered_singleton_aux}
      in ([pos], [i], thm) end

  | insert_sorted_into_sorted _ _ _ ([],_::_) = error "insert_sorted_into_sorted: range/program mismatch"
  | insert_sorted_into_sorted _ _ _ (_::_,[]) = error "insert_sorted_into_sorted: range/program mismatch"

  | insert_sorted_into_sorted ctxt memT (pos,i) (pos'::pos's, i'::i's) = let
    val n = linenum_of_rangestep pos
    val n' = linenum_of_rangestep pos' in
    if n = n'
    then case (pos,pos') of
        (If (_,side,range), If (_,side',range')) => let
            val _ = if side <> side' then error "Cannot join then/else branch of same if" else ()
            val (Block p) = i
            val (Block p') = i'
            (* thm: semantics (p@p') = semantics prog *)
            val (range,prog,thm) = join_with_ordered ctxt memT (shift_range1 range, p)
                                                               (shift_range1 range', p')
            val range' = If (n,side,unshift_range1 range) :: pos's
            val prog' = Block prog :: i's
            (* thm': semantics(i # i' # i's) = semantics prog' *)
            val thm' = @{thm insert_sorted_into_sorted_aux1} OF [thm]
          in (range',prog',thm') end
        | _ => error ("Duplicate instruction index " ^ string_of_int n)
    else if n < n' 
    then let
      val thm = infer ctxt [instruction_to_term memT i, program_to_term memT (i'::i's)] @{thm insert_into_ordered_prepend_aux}
      in (pos::pos'::pos's, i::i'::i's, thm) end

    else let
        (* semantics [i,i'] = semantics [i',i] *)
        val swap_thm = swap_instructions ctxt (instruction_to_term memT i) (instruction_to_term memT i')
        (* ii's_thm: semantics (i::i's) = semantics ii's *)
        val (nn's, ii's, ii's_thm) = insert_sorted_into_sorted ctxt memT (pos,i) (pos's,i's)
        val i'ii's = i' :: ii's
      
        val thm0 = infer ctxt [instruction_to_term memT i, instruction_to_term memT i', 
                               program_to_term memT i's, program_to_term memT ii's] 
                        @{thm insert_into_ordered_aux}
        val thm = thm0 OF [swap_thm, ii's_thm]
      in (pos'::nn's, i'ii's, thm) end
  end

(* Like insert_sorted_into_sorted but does not require that pos is sorted. *)
and insert_into_sorted ctxt memT (pos,instr) (range,prog) : range1 * instruction list * thm = let
  (* thm_instr': "semantics1 instr = semantics1 instr' *)
  val (pos', instr', thm_instr') = sort_instruction ctxt memT (pos,instr)
  (* thm_insert: "semantics (instr'#prog) = semantics prog' *)
  val (range', prog', thm_insert) = insert_sorted_into_sorted ctxt memT (pos', instr') (range,prog)
  (* thm: "semantics (instr'#prog) = semantics prog'" *)
  val thm = @{thm insert_into_sorted_aux1} OF [thm_instr', thm_insert]
  in (range', prog', thm) end

and sort_instruction ctxt memT (Line n, instr) = 
      (Line n, instr, infer ctxt [instruction_to_term memT instr] 
            @{thm sort_instruction_aux1})
  | sort_instruction ctxt memT (If (n,side,range), Block p) = let
      (* thm_instr': semantics p = semantics p' *)
      val (range',p',thm_p') = sort_program ctxt memT (shift_range1 range, p)
      val pos' = If (n, side, unshift_range1 range')
      (* thm: semantics1 (Block p) = semantics1 (Block p') *)
      val thm = @{thm sort_instruction_aux2} OF [thm_p']
      in (pos', Block p', thm) end
  | sort_instruction _ _ (r,i) = error ("sort_instruction: " ^ \<^make_string> r ^ "; " ^ \<^make_string> i)

(* join_with_ordered ctxt (range:range1, prog:term) (range':range1,prog':term)

  Inserts instructions from prog into prog'.
  (If possible.)
  prog, prog' are assumed to be extracted from the same program with range, range'.
  Assumes that range' is sorted. (But not range)

  Returns:
    range'': range of the returned program
    prog'': joined program
    thm: semantics (prog@prog') = semantics (prog')

 *)

and join_with_ordered ctxt memT ([]:range1,[]) (range':range1,prog':instruction list) :
                 range1 * instruction list * thm =
    (range', prog', infer ctxt [program_to_term memT prog'] @{thm join_with_ordered_empty_aux})
  | join_with_ordered ctxt memT (n::ns : range1, i::is) (range':range1,prog':instruction list) = let
        val (ns',is',thm_sort) = join_with_ordered ctxt memT (ns, is) (range',prog')
        val (nns',iis',thm_insert) = insert_into_sorted ctxt memT (n,i) (ns',is')
        val thm0 = infer ctxt [(*p*)program_to_term memT is, (*s*)program_to_term memT prog',
                               (*q*)program_to_term memT is', (*i*)instruction_to_term memT i, 
                               (*r*)program_to_term memT iis'] 
                  @{thm join_with_ordered_aux}
        val thm = thm0 OF [thm_sort, thm_insert]
      in (nns', iis', thm) end
  | join_with_ordered _ _ ([],_::_) _ = error "join_with_ordered: program/range mismatch"
  | join_with_ordered _ _ (_::_,[]) _ = error "join_with_ordered: program/range mismatch"

and sort_program ctxt memT (range,prog) : range1 * instruction list * thm = let
  val (range',prog',thm) = join_with_ordered ctxt memT (range,prog) ([],[])
  val thm' = @{thm sort_program_aux} OF [thm]
  in (range',prog',thm') end

(* fun sort_program _ ([]:range1,prog) : range1 * term * thm = 
        ([],prog,@{thm sort_program_empty_aux}) (* TODO: instantiate type! *)
  | sort_program ctxt (n::ns : range1, prog) = (case prog of
      Const(\<^const_name>\<open>Cons\<close>,_) $ i $ is => let
        val (ns',is',thm_sort) = sort_program ctxt (ns, is)
        val (nns',iis',thm_insert) = insert_into_ordered ctxt (n,i) (ns',is')
        val thm0 = infer ctxt [is, is', i, iis'] @{thm sort_program_aux}
        val thm = thm0 OF [thm_sort, thm_insert]
      in (nns', iis', thm) end
    | _ => raise TERM("sort_program: not a list",[prog])) *)



fun make_syntax_type (Type(name, Ts)) = Term.list_comb 
  (Const("\<^type>"^name, dummyT), map make_syntax_type Ts)
  | make_syntax_type T = raise TYPE("make_syntax_type: type variables not supported", [T], [])

fun tr_EXPR_like T _ e =   let
  fun replace i (Const(\<^syntax_const>\<open>_variable_prhl\<close>,_) $ Free(n,_)) =
        @{const eval_var(dummy,dummy)} $ Free(n, dummyT) $ Bound i
    | replace i (Const(\<^syntax_const>\<open>_the_memory_prhl\<close>,_)) = Bound i
    | replace _ (Const(\<^syntax_const>\<open>_the_memory1_prhl\<close>,_)) = error "$\<MM>1 not allowed in nonrelational expression"
    | replace _ (Const(\<^syntax_const>\<open>_the_memory2_prhl\<close>,_)) = error "$\<MM>2 not allowed in nonrelational expression"
    | replace _ (Const(\<^syntax_const>\<open>_variable_prhl\<close>,_) $ _) = error "$ must precede an identifier"
    | replace i (t1$t2) = replace i t1 $ replace i t2
    | replace i (Abs(n,t,body)) = Abs(n,t,replace (i+1) body)
    | replace _ t = t
  val e' = replace 0 e
  val t = Abs("mem",dummyT,e')
  in
    Const(\<^syntax_const>\<open>_constrain\<close>, dummyT) $ t $ make_syntax_type (dummyT --> T)
  end

fun tr_EXPR2_like T _ e =   let
  fun replace i (Const(\<^syntax_const>\<open>_variable_prhl\<close>,_) $ Free(n,_)) = let
        val len = String.size n
        val last = String.sub (n, len-1)
        val name = String.substring (n, 0, len-1)
        (* val _ = \<^print> (last,name) *)
        val lr = case last of #"1" => 1 | #"2" => 0 |
                    _ => error ("Variable must be indexed. ($"^n^"1 or $"^n^"2 instead of $"^n^")")
      in @{const eval_var(dummy,dummy)} $ Free(name, dummyT) $ Bound (i+lr) end
    | replace i (Const(\<^syntax_const>\<open>_the_memory1_prhl\<close>,_)) = Bound (i+1)
    | replace i (Const(\<^syntax_const>\<open>_the_memory2_prhl\<close>,_)) = Bound i
    | replace _ (Const(\<^syntax_const>\<open>_the_memory_prhl\<close>,_)) = error "$\<MM> not allowed in relational expression"
    | replace _ (Const(\<^syntax_const>\<open>_variable_prhl\<close>,_) $ _) = error "$ must precede an identifier"
    | replace i (t1$t2) = replace i t1 $ replace i t2
    | replace i (Abs(n,t,body)) = Abs(n,t,replace (i+1) body)
    | replace _ t = t
  val e' = replace 0 e
  val t = Abs("mem1",dummyT,Abs("mem2",dummyT,e'))
  in
    Const(\<^syntax_const>\<open>_constrain\<close>, dummyT) $ t $ make_syntax_type (dummyT --> dummyT --> T)
  end

fun print_tr_EXPR_like _ (Abs(_,_,body)) = let
    fun tr i ((c as Const(\<^const_syntax>\<open>eval_var\<close>,_)) $ (x as Const(\<^syntax_const>\<open>_free\<close>,_) $ Free _) $ Bound i') =
          if i=i' then Const(\<^syntax_const>\<open>_variable_prhl\<close>,dummyT) $ x
          else c $ tr i x $ Bound i'
      | tr i ((c as Const(\<^const_syntax>\<open>eval_var\<close>,_)) $ (x as Const _) $ Bound i') =
          if i=i' then Const(\<^syntax_const>\<open>_variable_prhl\<close>,dummyT) $ x
          else c $ tr i x $ Bound i'
      | tr i (Bound i') = if i=i' then Const(\<^syntax_const>\<open>_the_memory_prhl\<close>,dummyT)
                          else Bound i'
      | tr i (t1$t2) = tr i t1 $ tr i t2
      | tr i (Abs(n,T,t)) = Abs(n, T, tr (i+1) t)
      | tr _ (v as Free _) = v
      | tr _ (v as Var _) = v
      | tr _ (c as Const _) = c
    in tr 0 body end
  | print_tr_EXPR_like (_:Proof.context) e = e $ Const(\<^syntax_const>\<open>_the_memory_prhl\<close>,dummyT)

fun same_weight_tac ctxt = (* Raw_Simplifier.rewrite_goal_tac ctxt @{thms
      fst_conv[THEN eq_reflection] snd_conv[THEN eq_reflection]
      weight_semantics_Nil[THEN eq_reflection]
      weight_semantics_Set_cons[THEN eq_reflection]
      }
      THEN' resolve_tac ctxt @{thms refl} *)
  resolve_tac ctxt @{thms weight_semantics_Nil same_weight1
    weight1_cons weight1_if weight1_Set}

fun wp_tac ctxt = (* print_subgoal_tac ctxt "wp_tac" THEN' *) resolve_tac ctxt 
  @{thms wp_IfThenElse_cons wp_Set_cons wp_Sample_cons wp_Block_cons wp_Assert_cons wp_skip}

fun DETERM' tac i = DETERM (tac i)

fun independence_split_tac ctxt = SUBGOAL (fn (t,i) => let
  val (x,T,a,b) = case bool_of_prop' 0 t of Const(\<^const_name>\<open>independent_of\<close>,_) $ Abs(x,T, a $ b) $ _ => (x,T,a,b)
                    | _ => raise Match
(* val _ = \<^print> (x,T,a,b) *)
  val a' = Abs(x,T,a) |> Thm.cterm_of ctxt
  val b' = Abs(x,T,b) |> Thm.cterm_of ctxt
  val rule = Drule.infer_instantiate ctxt 
                  [(("a",0),a'),(("b",0),b')] @{thm independent_of_split}  
(* val _ = \<^print> rule *)
  in resolve_tac ctxt [rule] i end
  handle Match => no_tac)
(*   (fn ctxt => match_tac ctxt @{thms independent_of_split})
  |> Forward_Hoare_Utils.no_match_tactic \<^context> 1 "independent_of (\<lambda>a b. b) _"
  |> Forward_Hoare_Utils.no_match_tactic \<^context> 2 "independent_of (\<lambda>m. m) _" *)

fun print_subgoal_tac ctxt = SUBGOAL (fn (t,i) => 
  (tracing (string_of_int i ^ ": " ^ Syntax.string_of_term ctxt t); all_tac))

fun independence_tac_step ctxt = 
  (* print_subgoal_tac ctxt THEN' *)
  DETERM' (match_tac ctxt (@{thms 
  independent_of_const independent_of_var
  independent_of_prog_Set_cons independent_of_prog_Sample_cons
  independent_of_prog_empty}
     @ Named_Theorems.get ctxt \<^named_theorems>\<open>independence\<close>)
  ORELSE' independence_split_tac ctxt)

fun independence_tac ctxt i = 
  (* REPEAT_ALL_NEW (independence_tac_step ctxt) *)
  (independence_tac_step ctxt 
    THEN_ALL_NEW independence_tac ctxt) i

fun split_invariant_implications _ impl = let
  fun split1 impl = Forward_Hoare.filter_OF 
    @{thms split_invariant_implication_conj1 split_invariant_implication_conj2
           split_invariant_implication_all1 split_invariant_implication_all2
           split_invariant_implication_ball1 split_invariant_implication_ball2
           split_invariant_implication_imp1 split_invariant_implication_imp2
      } [impl]
  fun split impl = case split1 impl of 
    [] => [impl]
    | impls => maps split impls
  in split impl end

structure Logic1 = Hoare_Logic(
  val binding = \<^binding>\<open>prhl\<close>
  structure Utils = Forward_Hoare_Utils()
  open Utils

  type options = {memory_type: typ option, 
                  util_options: Utils.options,
                  left_program: string option,
                  right_program: string option}
  val default_options = {memory_type = NONE, util_options = Utils.default_options,
    left_program = NONE, right_program = NONE}
  fun set_memory_type T ({util_options,left_program,right_program,...}:options) : options = {memory_type = SOME T, util_options=util_options, left_program=left_program, right_program=right_program}
  fun set_left_program name ({util_options,memory_type,right_program,...}:options) : options = {memory_type = memory_type, util_options=util_options, left_program=SOME name, right_program=right_program}
  fun set_right_program name ({util_options,memory_type,left_program,...}:options) : options = {memory_type = memory_type, util_options=util_options, right_program=SOME name, left_program=left_program}
  fun map_util_options f ({util_options, memory_type,left_program,right_program}:options) : options = {util_options = f util_options, memory_type = memory_type, left_program=left_program, right_program=right_program}
  fun set_option "memory" typ_str ctxt m = let
        val T = Syntax.read_typ ctxt (Syntax.implode_input typ_str)
        val T = Morphism.typ m T
        in set_memory_type T end
(* TODO: check in left/right whether this is one of "our" programs *)
    | set_option "left" name ctxt _ = 
        set_left_program (read_program_name_as_name (Context.Proof ctxt) (Input.source_content name))
    | set_option "right" name ctxt _ = 
        set_right_program (read_program_name_as_name (Context.Proof ctxt) (Input.source_content name))
    | set_option name content ctxt m = map_util_options (Utils.set_option name content ctxt m)

  fun the_left_program options = options |> #left_program |> the' (fn _ => "No left program configured. Use 'hoare (tmp_logic) config left = name'")
  fun the_right_program options = options |> #right_program |> the' (fn _ => "No right program configured. Use 'hoare (tmp_logic) config left = name'")

  datatype range = Range of range1p |
    Range2 of range1p * range1p

  fun extract_range ctxt (Range (progname,range)) = let
        val prog = get_my_program ctxt progname
        val memT = fastype_of prog |> dest_programT
        val prog = term_to_program prog
        val extr = extract_range1 ctxt memT prog range
        val extr = program_to_term memT extr
      in extr end
    | extract_range ctxt (Range2 ((p1,r1),(p2,r2))) = let
        val t1 = extract_range ctxt (Range (p1,r1))
        val t2 = extract_range ctxt (Range (p2,r2))
      in HOLogic.mk_prod (t1,t2) end

  fun program_term_typ options = 
    programT (#memory_type options |> the' (fn _ => "Memory type not set. Use \"Hoare config memory = <typ>\"."))
  fun invariant_typ options = 
    (#memory_type options |> the' (fn _ => "Memory type not set. Use \"Hoare config memory = <typ>\".")) --> dummyT

(*   fun pretty_range1 [] = Pretty.str "\<emptyset>"
    | pretty_range1 range = Pretty.commas (range |> map (string_of_int #> Pretty.str)) |> Pretty.block
  fun pretty_range _ (Range (_,range)) = pretty_range1 range
    | pretty_range _ (Range2 ((_,range1),(_,range2))) = 
        Pretty.block [pretty_range1 range1, Pretty.str " ~ ", pretty_range1 range2] *)
  fun pretty_rangestep (Line i) = (i |> string_of_int |> Pretty.str)
    | pretty_rangestep (If (i,side,range)) = Pretty.block
          [i |> string_of_int |> Pretty.str,
           (if side then "t" else "f") |> Pretty.str,
           Pretty.str "(",
           pretty_range1 range,
           Pretty.str ")"]
  and pretty_range1 ([] : range1) = Pretty.str "\<emptyset>"
    | pretty_range1 (range) = Pretty.commas (range |> map pretty_rangestep) |> Pretty.block
  fun pretty_range1p ((_,r) : range1p) = pretty_range1 r
  fun pretty_range _ (Range range) = pretty_range1p range
    | pretty_range _ (Range2 (range1,range2)) = 
      Pretty.block [pretty_range1p range1, Pretty.str " ~ ", pretty_range1p range2]

  fun check_program _ prog = (HOLogic.dest_list prog; ())
    handle TERM _ => error "Program must be a list of instructions"

  fun postcondition_default_const T = let
    val progT = programT T
    val invT = invariantT T
  in Const(\<^const_name>\<open>postcondition_default\<close>, progT --> invT --> invT) end

  fun postcondition_default2_const T T' = let
    (* val progT = program2T T T' *)
    val invT = invariant2T T T'
  in Const(\<^const_name>\<open>postcondition_default2\<close>, programT T --> programT T' --> invT --> invT) end

  fun postcondition_default1 program_fragment pre = let
    val T = dest_invariantT "postcondition_default" (fastype_of pre)
    val post = postcondition_default_const T $ program_fragment $ pre
    fun tac ctxt = resolve_tac ctxt @{thms postcondition_default_valid} 1
    in
      (post, tac)
    end

  fun postcondition_default2 program_fragment pre = let
    val (T,T') = dest_invariant2T "postcondition_default2" (fastype_of pre)
    val (p1,p2) = HOLogic.dest_prod program_fragment
    val post = postcondition_default2_const T T' $ p1 $ p2 $ pre
    fun tac ctxt = resolve_tac ctxt @{thms postcondition_default2_valid} 1
    in
      (post, tac)
    end

  fun postcondition_default program_fragment pre = 
    if is_prod (fastype_of program_fragment) then
      postcondition_default2 program_fragment pre
    else
      postcondition_default1 program_fragment pre

  fun postcondition_rnd_parse ctxt program_fragment pre = let
    val (prog1,prog2) = HOLogic.dest_prod program_fragment
                        handle TERM _ => error "Postcondition rnd only works for relational Hoare judgments"
    val prog1s = HOLogic.dest_list prog1 |> the_single
                 handle TERM _ => error "Left program must consist of a single statement"
                 handle List.Empty => error "Left program must consist of a single statement"
    val prog2s = HOLogic.dest_list prog2 |> the_single
                 handle TERM _ => error "Right program must consist of a single statement"
                 handle List.Empty => error "Right program must consist of a single statement"
    val x1 = case prog1s of (Const(\<^const_name>\<open>Sample\<close>, _) $ x $ _) => x
              | _ => error "Left program must consist of a Sample statement"
    val x2 = case prog2s of (Const(\<^const_name>\<open>Sample\<close>, _) $ x $ _) => x
              | _ => error "Right program must consist of a Sample statement"
    val (mem1T,x1T) = fastype_of x1 |> dest_varT "postcondition_rnd_parse"
    val (mem2T,x2T) = fastype_of x2 |> dest_varT "postcondition_rnd_parse"
    fun tac ctxt = resolve_tac ctxt @{thms postcondition_rnd_valid} 1
              (* THEN resolve_tac ctxt @{thms refl} 1 *)
    fun mk_postcondition coupling_str = let
      val couplingT = mem1T --> mem2T --> (HOLogic.mk_prodT (x1T,x2T) |> spmfT)
      val coupling = read_term_typed ctxt couplingT coupling_str
      val pc_const = Const(\<^const_name>\<open>postcondition_rnd\<close>, 
            couplingT --> varT mem1T x1T --> varT mem2T x2T
                      --> invariant2T mem1T mem2T --> invariant2T mem1T mem2T)
      val pc = pc_const $ coupling $ x1 $ x2 $ pre
      in (pc,tac) end
    in Scan.lift Parse.term >> mk_postcondition end

  val postcondition_generators = [
    ("default", fn _ => fn prog => fn pre => Scan.succeed (postcondition_default prog pre) |> Scan.lift),
    ("rnd", postcondition_rnd_parse)
    ]


  val tilde = Parse.sym_ident :-- (fn "~" => Scan.succeed () | _ => Scan.fail) >> #1;
  val emptyset = Parse.sym_ident :-- (fn "\<emptyset>" => Scan.succeed () | _ => Scan.fail) >> #1;

  val truefalse_parser = 
    Parse.short_ident :|-- (fn "t" => Scan.succeed true | "f" => Scan.succeed false | _ => Scan.fail)
  fun range_step_parser toks = 
    (Parse.nat -- truefalse_parser --| Parse.$$$ "(" -- range1_parser --| Parse.$$$ ")"
      >> (fn ((line,tf),r) => If (line,tf,r))
     || Parse.nat >> Line) toks
  and range1_parser toks = 
    (Parse.list1 range_step_parser || (emptyset >> K [])) toks

  fun read_range (options:options) _ : range context_parser = 
    Scan.lift (range1_parser -- Scan.option (tilde |-- range1_parser))
      >> (fn (indices,NONE) => Range (get_current_program_name (#util_options options), indices)
           | (indices1,SOME indices2) => Range2 ((the_left_program options, indices1), (the_right_program options, indices2)))

  fun check_invariant _ _ = ()

  fun hoare_const T = let
    val invT = invariantT T
    val progT = programT T
  in Const(\<^const_name>\<open>hoare\<close>, invT --> progT --> invT --> HOLogic.boolT) end

  fun rhoare_const T T' = let
    val invT = invariant2T T T'
    val progT = programT T
    val progT' = programT T'
  in Const(\<^const_name>\<open>rhoare\<close>, invT --> progT --> progT' --> invT --> HOLogic.boolT) end

  fun hoare_thm _ pre prog post = 
    if not (is_prod (fastype_of prog)) then
      hoare_const (dest_invariantT "hoare_thm" (fastype_of pre)) $
          pre $ prog $ post |> HOLogic.mk_Trueprop
    else
      let 
(* val _ = \<^print>("hoare_thm",prog  |> Thm.cterm_of ctxt) *)
          val (T1,T2) = dest_invariant2T "hoare_thm" (fastype_of pre)
          (* val prog12T = HOLogic.mk_prodT (programT T1, programT T2) *)
          (* val prog1 = Const(\<^const_name>\<open>fst\<close>, prog12T --> programT T1) $ prog *)
          (* val prog2 = Const(\<^const_name>\<open>snd\<close>, prog12T --> programT T2) $ prog *)
          val (prog1,prog2) = HOLogic.dest_prod prog
      in rhoare_const T1 T2 $ pre $ 
        prog1 $ prog2 $ post |> HOLogic.mk_Trueprop end

  fun join_hoare ctxt _ (Range (prog12,range12)) _ (Range (prog23,range23)) _ thm12 thm23 = let
    val _ = if prog12 <> prog23 then error ("Trying to join Hoare judgments from different programs " ^ prog12 ^ " and " ^ prog23) else ()
    val p12 = extract_range ctxt (Range (prog12,range12))
    val p23 = extract_range ctxt (Range (prog12,range23))
    (* hoare invariant1 (p12@p23) invariant3 *)
    val hoare_append = (@{thm hoare_seq} OF [thm12, thm23])
    val prog = get_my_program ctxt prog12
    val progT = fastype_of prog
    val memT = progT |> dest_programT
    val p12_p23 = Const(\<^const_name>\<open>append\<close>, progT --> progT --> progT) $ p12 $ p23
    (* p12@p23 \<equiv> p13 *)
    val p13_thm = append_conv (Thm.cterm_of ctxt p12_p23)
    val p13 = Thm.rhs_of p13_thm |> Thm.term_of
    val (range13,_,sorted_thm) = sort_program ctxt memT (range12@range23, term_to_program p13)
    (* val _ = sorted_thm |> \<^print> *)
    val thm = @{thm join_hoare} OF [hoare_append, p13_thm, sorted_thm]
  in (Range (prog12,range13),thm) end

  | join_hoare ctxt _ (Range2 ((prog12,range12),(prog12',range12')))
                    _ (Range2 ((prog23,range23),(prog23',range23'))) _ thm12 thm23 = let
    val _ = if prog12 <> prog23 then error ("Trying to join Hoare judgments from different left programs " ^ prog12 ^ " and " ^ prog23) else ()
    val _ = if prog12' <> prog23' then error ("Trying to join Hoare judgments from different right left programs " ^ prog12 ^ " and " ^ prog23) else ()
    val p12 = extract_range ctxt (Range (prog12,range12))
    val p23 = extract_range ctxt (Range (prog12,range23))
    val p12' = extract_range ctxt (Range (prog12',range12'))
    val p23' = extract_range ctxt (Range (prog12',range23'))
    (* rhoare invariant1 (p12@p23) (p12'@p23') invariant3 *)
    val hoare_append = (@{thm rhoare_seq} OF [thm12, thm23])
    val prog = get_my_program ctxt prog12
    val prog' = get_my_program ctxt prog12'
    val progT = fastype_of prog
    val progT' = fastype_of prog'
    val memT = dest_programT progT
    val memT' = dest_programT progT'
    val p12_p23 = Const(\<^const_name>\<open>append\<close>, progT --> progT --> progT) $ p12 $ p23
    val p12_p23' = Const(\<^const_name>\<open>append\<close>, progT' --> progT' --> progT') $ p12' $ p23'
    (* p12@p23 \<equiv> p13 *)
    val p13_thm = append_conv (Thm.cterm_of ctxt p12_p23)
    val p13 = Thm.rhs_of p13_thm |> Thm.term_of
    (* p12'@p23' \<equiv> p13' *)
    val p13_thm' = append_conv (Thm.cterm_of ctxt p12_p23')
    val p13' = Thm.rhs_of p13_thm' |> Thm.term_of
    val (range13,_,sorted_thm) = sort_program ctxt memT (range12@range23, term_to_program p13)
    val (range13',_,sorted_thm') = sort_program ctxt memT' (range12'@range23', term_to_program p13')
    (* val _ = sorted_thm |> \<^print> *)
    val thm = @{thm join_rhoare} OF [hoare_append, p13_thm, p13_thm', sorted_thm, sorted_thm']
  in (Range2 ((prog12,range13),(prog12',range13')),thm) end

  | join_hoare _ _ _ _ _ _ _ _ =
    error "Joining relational and non-relational Hoare judgments not supported"


  fun invariant_implication _ inv1 inv2 = let
    val inv1T = fastype_of inv1
    (* val inv2T = fastype_of inv2 *)
    (* val _ = if inv1T <> inv2T then raise (TYPE("Comparing invariants of different types", [inv1T,inv2T], [])) else () *)
  in case is_rinvT inv1T of
    false => let
      val memT = inv1T |> dest_invariantT "invariant_implication"
      in 
         HOLogic.all_const memT $ Abs("mem",memT, 
           HOLogic.mk_imp (inv1 $ Bound 0, inv2 $ Bound 0))
      end
  | true => let
      val (mem1T,mem2T) = dest_invariant2T "invariant_implication" inv1T
      in
         HOLogic.all_const mem1T $ Abs("mem1",mem1T, 
           HOLogic.all_const mem2T $ Abs("mem2",mem2T,
            HOLogic.mk_imp (inv1 $ Bound 1 $ Bound 0, inv2 $ Bound 1 $ Bound 0)))
      end
  end
  
  fun invariant_implication_lhs (Const(\<^const_name>\<open>All\<close>,_) $ Abs(_,_, (Const(\<^const_name>\<open>All\<close>,_) $ Abs(_,_, Const(\<^const_name>\<open>implies\<close>,_) $ (inv $ _ $ _) $ _)))) = inv
    | invariant_implication_lhs (Const(\<^const_name>\<open>All\<close>,_) $ Abs(_,_, Const(\<^const_name>\<open>implies\<close>,_) $ (inv $ _ ) $ _)) = inv
    | invariant_implication_lhs t = raise TERM("invariant_implication_lhs", [t])

  fun invariant_parse_translation ctxt other_inv t =
    if is_rinvT (fastype_of other_inv)
    then tr_EXPR2_like HOLogic.boolT ctxt t
    else tr_EXPR_like HOLogic.boolT ctxt t

  fun invariant_consequences thm ctxt = 
    Forward_Hoare.filter_OF @{thms mk_invariant_consequence1 mk_invariant_consequence2} [thm]
    |> maps (split_invariant_implications ctxt)

  val subgoal_tactics = [("wp_tac",wp_tac),("independence_tac",independence_tac),
    ("same_weight_tac", same_weight_tac)]


  fun merge_hoare ctxt precondition (args) = let
  in error ("nyi: merge_hoare" ^ \<^make_string> (precondition,args)) end
)

end

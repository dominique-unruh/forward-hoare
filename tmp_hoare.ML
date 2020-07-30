structure Tmp_Hoare =
struct

open Forward_Hoare

fun dest_listT (Type(\<^type_name>\<open>list\<close>, [T])) = T
  | dest_listT T = raise TYPE("dest_listT", [T], [])

fun instructionT T = Type(\<^type_name>\<open>instruction\<close>, [T])
fun dest_instructionT (Type(\<^type_name>\<open>instruction\<close>, [T])) = T
  | dest_instructionT T = raise TYPE("dest_instructionT", [T], [])
  
fun programT T = instructionT T |> HOLogic.listT
fun dest_programT T = dest_listT T |> dest_instructionT
fun invariantT T = T --> HOLogic.boolT
fun dest_invariantT (Type(\<^type_name>\<open>fun\<close>, [T, \<^typ>\<open>bool\<close>])) = T
  | dest_invariantT T = raise TYPE("dest_invariantT", [T], [])

fun varT T T' = Type(\<^type_name>\<open>var\<close>, [T,T'])

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
      val error2 = "\nDeclare a suitable rule for it and declare attribute [independence]"
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

fun swap_instructions ctxt a b = let
  val T = fastype_of a
  val prop = Const(\<^const_name>\<open>instructions_commute\<close>, T --> T --> HOLogic.boolT) $ a $ b |> HOLogic.mk_Trueprop
  fun tac ctxt = (resolve_tac ctxt @{thms commute_indep} 
      THEN_ALL_NEW indep_tac ctxt) 1
  val thm = Goal.prove ctxt [] [] prop (fn {context=ctxt,...} => tac ctxt)
  in thm end

fun insert_into_ordered ctxt (n,i) ([],_) = let
      val thm = infer ctxt [i] @{thm insert_into_ordered_singleton_aux}
      in ([n], HOLogic.mk_list (fastype_of i) [i], thm) end
  | insert_into_ordered ctxt (n,i) (n'::n's, is) =
    if n = n'
    then error ("Duplicate instruction index " ^ string_of_int n)
    else if n < n' 
    then let
      val thm = Drule.infer_instantiate' ctxt [i |> Thm.cterm_of ctxt |> SOME, is |> Thm.cterm_of ctxt |> SOME] @{thm insert_into_ordered_prepend_aux}
      in (n::n'::n's, HOLogic.cons_const (fastype_of i) $ i $ is, thm) end

    else case is of
      Const(\<^const_name>\<open>Cons\<close>,_) $ i' $ i's => let
        (* semantics [i,i'] = semantics [i',i] *)
        val swap_thm = swap_instructions ctxt i i'
        (* ii's_thm: semantics (i::i's) = semantics ii's *)
        val (nn's, ii's, ii's_thm) = insert_into_ordered ctxt (n,i) (n's,i's)
        val i'ii's = HOLogic.cons_const (fastype_of i') $ i' $ ii's
      
        val thm0 = infer ctxt [i, i', i's, ii's] @{thm insert_into_ordered_aux}
        val thm = thm0 OF [swap_thm, ii's_thm]
      in (n'::nn's, i'ii's, thm) end
    | _ => raise TERM("insert_into_ordered: not a list",[is])

fun sort_program _ ([],prog) = ([],prog,@{thm sort_program_empty_aux})
  | sort_program ctxt (n::ns, prog) = (case prog of
      Const(\<^const_name>\<open>Cons\<close>,_) $ i $ is => let
        val (ns',is',thm_sort) = sort_program ctxt (ns, is)
        val (nns',iis',thm_insert) = insert_into_ordered ctxt (n,i) (ns',is')
        val thm0 = infer ctxt [is, is', i, iis'] @{thm sort_program_aux}
        val thm = thm0 OF [thm_sort, thm_insert]
      in (nns', iis', thm) end
    | _ => raise TERM("sort_program: not a list",[prog]))

structure Logic = Hoare_Logic(
  val binding = \<^binding>\<open>tmp_hoare\<close>

  type options = {memory_type: typ option}
  val default_options = {memory_type = NONE}
  fun set_memory_type T (_:options) : options = {memory_type = SOME T}
  fun set_option "memory" typ_str ctxt m = let
    val T = Syntax.read_typ ctxt typ_str
    val T = Morphism.typ m T
    in set_memory_type T end
    | set_option name _ _ _ = error ("Unknown option " ^ name)
    

  type range = int list
  fun program_term_typ options = 
    programT (#memory_type options |> the' (fn _ => "Memory type not set. Use \"Hoare config memory = <typ>\"."))
  fun invariant_typ options = 
    invariantT (#memory_type options |> the' (fn _ => "Memory type not set. Use \"Hoare config memory = <typ>\"."))

  fun pretty_range _ range = Pretty.commas (range |> map (string_of_int #> Pretty.str)) |> Pretty.block

  fun check_program _ prog = (HOLogic.dest_list prog; ())
    handle TERM _ => error "Program must be a list of instructions"

  fun postcondition_default_const T = let
    val progT = programT T
    val invT = invariantT T
  in Const(\<^const_name>\<open>postcondition_default\<close>, progT --> invT --> invT) end

  fun postcondition_default program_fragment pre = let
    val T = dest_invariantT (fastype_of pre)
    val post = postcondition_default_const T $ program_fragment $ pre
    fun tac ctxt = resolve_tac ctxt @{thms postcondition_default_valid} 1
    in
      (post, tac)
    end

  val postcondition_generators = Symtab.make [
    ("default", Scan.succeed postcondition_default |> Scan.lift)]

  fun extract_range prog range = let
    val prog' = prog |> HOLogic.dest_list
    val extr' = map (fn i => nth prog' (i-1)) range
  in HOLogic.mk_list (fastype_of prog |> dest_listT) extr' end

  fun read_range _ = Parse.list1 Parse.nat |> Scan.lift

(* TODO rename to check_range and have unit return type *)
  fun valid_range prog range = let
    val len = length (prog |> HOLogic.dest_list)
    val _ = range |> List.app (fn i => if i <= 0 
            then error ("Range contains invalid index " ^ string_of_int i ^ " <= 0")
            else ()) 
    val _ = range |> List.app (fn i => if i > len 
            then error ("Range contains invalid index " ^ string_of_int i ^ " > " ^ string_of_int len ^ " (program length)")
            else ()) 
    val _ = if is_unique_sorted range then ()
            else error ("Range is not sorted")
  in true end

  fun check_invariant _ _ = ()

  fun hoare_const T = let
    val invT = invariantT T
    val progT = programT T
  in Const(\<^const_name>\<open>hoare\<close>, invT --> progT --> invT --> HOLogic.boolT) end

  fun hoare_thm _ pre prog post = hoare_const (dest_invariantT (fastype_of pre)) $
    pre $ prog $ post |> HOLogic.mk_Trueprop

  fun join_hoare ctxt program _ range12 _ range23 _ thm12 thm23 = let
    val p12 = extract_range program range12
    val p23 = extract_range program range23
    (* hoare invariant1 (p12@p23) invariant3 *)
    val hoare_append = (@{thm hoare_seq} OF [thm12, thm23])
    val progT = fastype_of program
    val p12_p23 = Const(\<^const_name>\<open>append\<close>, progT --> progT --> progT) $ p12 $ p23
    (* p12@p23 \<equiv> p13 *)
    val p13_thm = append_conv (Thm.cterm_of ctxt p12_p23)
    val p13 = Thm.rhs_of p13_thm |> Thm.term_of
    val (range13,_,sorted_thm) = sort_program ctxt (range12@range23, p13)
    (* val _ = sorted_thm |> \<^print> *)
    val thm = @{thm join_hoare} OF [hoare_append, p13_thm, sorted_thm]
  in (range13,thm) end


  fun invariant_implication _ inv1 inv2 = let
    val memT = fastype_of inv1 |> dest_invariantT
  in 
     Logic.all_const memT $ Abs("mem",memT, 
      HOLogic.mk_imp (inv1 $ Bound 0, inv2 $ Bound 0) |> HOLogic.mk_Trueprop)
  end
)


end

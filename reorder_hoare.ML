structure Reorder_Hoare =
struct

open Forward_Hoare

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
  in simp_tac ctxt i end)

fun indep_tac ctxt = SUBGOAL (fn (t,i) => let
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
  )

fun swap_instructions ctxt a b = let
  val prop = \<^const>\<open>instructions_commute\<close> $ a $ b |> HOLogic.mk_Trueprop
  fun tac ctxt = resolve_tac ctxt @{thms commute_indep} 1
    THEN literal_neq_tac ctxt 3
    THEN indep_tac ctxt 2
    THEN indep_tac ctxt 1
  val thm = Goal.prove ctxt [] [] prop (fn {context=ctxt,...} => tac ctxt)
  in thm end

fun insert_into_ordered ctxt (n,i) ([],_) = let
      val thm = infer ctxt [i] @{thm insert_into_ordered_singleton_aux}
      in ([n], HOLogic.mk_list \<^typ>\<open>instruction\<close> [i], thm) end
  | insert_into_ordered ctxt (n,i) (n'::n's, is) =
    if n = n'
    then error ("Duplicate instruction index " ^ string_of_int n)
    else if n < n' 
    then let
      val thm = Drule.infer_instantiate' ctxt [i |> Thm.cterm_of ctxt |> SOME, is |> Thm.cterm_of ctxt |> SOME] @{thm insert_into_ordered_prepend_aux}
      in (n::n'::n's, HOLogic.cons_const \<^typ>\<open>instruction\<close> $ i $ is, thm) end

    else case is of
      Const(\<^const_name>\<open>Cons\<close>,_) $ i' $ i's => let
        (* semantics [i,i'] = semantics [i',i] *)
        val swap_thm = swap_instructions ctxt i i'
        (* ii's_thm: semantics (i::i's) = semantics ii's *)
        val (nn's, ii's, ii's_thm) = insert_into_ordered ctxt (n,i) (n's,i's)
        val i'ii's = HOLogic.cons_const \<^typ>\<open>instruction\<close> $ i' $ ii's
      
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
  val binding = \<^binding>\<open>reorder_hoare\<close>
  structure Utils = Forward_Hoare_Utils(val logic_name = Binding.name_of binding)
  open Utils

  type range = string * int list
  fun program_term_typ _ = \<^typ>\<open>program\<close>
  fun invariant_typ _ = \<^typ>\<open>invariant\<close>

(*   type options = unit
  val default_options = ()
  fun set_option _ _ _ _ _ = error "Logic reorder_hoare has no options" *)

  fun pretty_range _ (_,range) = Pretty.commas (range |> map (string_of_int #> Pretty.str)) |> Pretty.block

  fun check_program _ prog = (HOLogic.dest_list prog; ())
    handle TERM _ => error "Program must be a list of instructions"

  fun postcondition_default program_fragment pre = let
    val post = \<^const>\<open>postcondition_default\<close> $ program_fragment $ pre
    fun tac ctxt = resolve_tac ctxt @{thms postcondition_default_valid} 1
    in
      (post, tac)
    end

  val postcondition_generators = Symtab.make [
    ("default", Scan.succeed postcondition_default |> Scan.lift)]

  fun extract_range ctxt (prog,range) = let
    val prog' = get_my_program ctxt prog |> HOLogic.dest_list
    val extr' = map (fn i => nth prog' (i-1)) range
  in HOLogic.mk_list \<^typ>\<open>instruction\<close> extr' end

  fun read_range options _ = 
    Scan.lift (Parse.list1 Parse.nat)
      >> (fn indices => (get_current_program_name options, indices))

(* (* TODO rename to check_range and have unit return type *)
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
  in true end *)

  fun check_invariant _ _ = ()

  fun hoare_thm _ pre prog post = \<^const>\<open>hoare\<close> $ pre $ prog $ post |> HOLogic.mk_Trueprop

  fun join_hoare ctxt _ (prog12,range12) _ (prog23,range23) _ thm12 thm23 = let
    val _ = if prog12 <> prog23 then error ("Trying to join Hoare judgments from different programs " ^ prog12 ^ " and " ^ prog23) else ()
    val p12 = extract_range ctxt (prog12,range12)
    val p23 = extract_range ctxt (prog12,range23)
    (* hoare invariant1 (p12@p23) invariant3 *)
    val hoare_append = (@{thm hoare_seq} OF [thm12, thm23])
    val p12_p23 = @{const append(instruction)} $ p12 $ p23
    (* p12@p23 \<equiv> p13 *)
    val p13_thm = append_conv (Thm.cterm_of ctxt p12_p23)
    val p13 = Thm.rhs_of p13_thm |> Thm.term_of
    val (range13,_,sorted_thm) = sort_program ctxt (range12@range23, p13)
    (* val _ = sorted_thm |> \<^print> *)
    val thm = @{thm join_hoare} OF [hoare_append, p13_thm, sorted_thm]
  in ((prog12,range13),thm) end


  fun invariant_implication _ inv1 inv2 =
    Logic.all_const \<^typ>\<open>mem\<close> $ Abs("mem",\<^typ>\<open>mem\<close>, 
      HOLogic.mk_imp (inv1 $ Bound 0, inv2 $ Bound 0) |> HOLogic.mk_Trueprop)
)


end

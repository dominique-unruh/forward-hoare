structure Tmp_Hoare =
struct

(* TODO

   Uniform syntax for selecting logic (right after "hoare" keyword)

   Options can be given locally (e.g., when defining a program)?

   Use invariant syntax translation when declaring invariants

 *)

open Forward_Hoare

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

fun make_syntax_type (Type(name, Ts)) = Term.list_comb 
  (Const("\<^type>"^name, dummyT), map make_syntax_type Ts)

fun tr_EXPR_like T ctxt e =   let
  fun replace i (Const(\<^syntax_const>\<open>_variable_tmp_hoare\<close>,_) $ Free(n,_)) =
        @{const eval_var(dummy,dummy)} $ Free(n, dummyT) $ Bound i
    | replace i (Const(\<^syntax_const>\<open>_variable_tmp_hoare\<close>,_) $ _) = error "$ must precede an identifier"
    | replace i (t1$t2) = replace i t1 $ replace i t2
    | replace i (Abs(n,t,body)) = Abs(n,t,replace (i+1) body)
    | replace i t = t
  val e' = replace 0 e
  val t = Abs("mem",dummyT,e')
  in
    Const(\<^syntax_const>\<open>_constrain\<close>, dummyT) $ t $ make_syntax_type (dummyT --> T)
  end

fun tr_EXPR2_like T ctxt e =   let
  fun replace i (Const(\<^syntax_const>\<open>_variable_tmp_hoare\<close>,_) $ Free(n,_)) = let
        val len = String.size n
        val last = String.sub (n, len-1)
        val name = String.substring (n, 0, len-1)
        (* val _ = \<^print> (last,name) *)
        val lr = case last of #"1" => 1 | #"2" => 0 |
                    _ => error ("Variable must be indexed. ($"^n^"1 or $"^n^"2 instead of $"^n^")")
      in @{const eval_var(dummy,dummy)} $ Free(name, dummyT) $ Bound (i+lr) end
    | replace i (Const(\<^syntax_const>\<open>_variable_tmp_hoare\<close>,_) $ _) = error "$ must precede an identifier"
    | replace i (t1$t2) = replace i t1 $ replace i t2
    | replace i (Abs(n,t,body)) = Abs(n,t,replace (i+1) body)
    | replace i t = t
  val e' = replace 0 e
  val t = Abs("mem1",dummyT,Abs("mem2",dummyT,e'))
  in
    Const(\<^syntax_const>\<open>_constrain\<close>, dummyT) $ t $ make_syntax_type (dummyT --> dummyT --> T)
  end


fun wp_tac ctxt = (* print_subgoal_tac ctxt "wp_tac" THEN' *) resolve_tac ctxt @{thms wp_Set_cons1 wp_Set_cons2 wp_skip12}

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
  val binding = \<^binding>\<open>tmp_hoare\<close>
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
        val T = Syntax.read_typ ctxt typ_str
        val T = Morphism.typ m T
        in set_memory_type T end
    | set_option "left" name ctxt _ = let val name' = YXML.content_of name in
        get_my_program ctxt name'; set_left_program name' end
    | set_option "right" name ctxt _ = let val name' = YXML.content_of name in
        get_my_program ctxt name'; set_right_program name' end
    | set_option name content ctxt m = map_util_options (Utils.set_option name content ctxt m)

  fun the_left_program options = options |> #left_program |> the' (fn _ => "No left program configured. Use 'hoare (tmp_logic) config left = name'")
  fun the_right_program options = options |> #right_program |> the' (fn _ => "No right program configured. Use 'hoare (tmp_logic) config left = name'")

  datatype range = Range of string * int list | Range2 of string * int list * string * int list

  fun program_term_typ options = 
    programT (#memory_type options |> the' (fn _ => "Memory type not set. Use \"Hoare config memory = <typ>\"."))
  fun invariant_typ options = 
    (#memory_type options |> the' (fn _ => "Memory type not set. Use \"Hoare config memory = <typ>\".")) --> dummyT

  fun pretty_range1 [] = Pretty.str "\<emptyset>"
    | pretty_range1 range = Pretty.commas (range |> map (string_of_int #> Pretty.str)) |> Pretty.block
  fun pretty_range _ (Range (_,range)) = pretty_range1 range
    | pretty_range _ (Range2 (_,range1,_,range2)) = 
        Pretty.block [pretty_range1 range1, Pretty.str " ~ ", pretty_range1 range2]

  fun check_program _ prog = (HOLogic.dest_list prog; ())
    handle TERM _ => error "Program must be a list of instructions"

  fun postcondition_default_const T = let
    val progT = programT T
    val invT = invariantT T
  in Const(\<^const_name>\<open>postcondition_default\<close>, progT --> invT --> invT) end

  fun postcondition_default2_const T T' = let
    val progT = program2T T T'
    val invT = invariant2T T T'
  in Const(\<^const_name>\<open>postcondition_default2\<close>, progT --> invT --> invT) end

  fun postcondition_default1 program_fragment pre = let
    val T = dest_invariantT "postcondition_default" (fastype_of pre)
    val post = postcondition_default_const T $ program_fragment $ pre
    fun tac ctxt = resolve_tac ctxt @{thms postcondition_default_valid} 1
    in
      (post, tac)
    end

  fun postcondition_default2 program_fragment pre = let
    val (T,T') = dest_invariant2T "postcondition_default2" (fastype_of pre)
    val post = postcondition_default2_const T T' $ program_fragment $ pre
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
                 handle List.Empty => error "right program must consist of a single statement"
    val (x1,e1) = case prog1s of (Const(\<^const_name>\<open>Sample\<close>, _) $ x1 $ e1) => (x1,e1)
              | _ => error "Left program must consist of a Sample statement"
    val (x2,e2) = case prog1s of (Const(\<^const_name>\<open>Sample\<close>, _) $ x2 $ e2) => (x2,e2)
              | _ => error "Right program must consist of a Sample statement"
    val (mem1T,x1T) = fastype_of x1 |> dest_varT "postcondition_rnd_parse"
    val (mem2T,x2T) = fastype_of x1 |> dest_varT "postcondition_rnd_parse"
    fun tac ctxt = resolve_tac ctxt @{thms postcondition_rnd_valid} 1
              THEN resolve_tac ctxt @{thms refl} 1
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

  fun extract_range ctxt (Range (progname,range)) = let
        val prog = get_my_program ctxt progname
        val prog' = prog |> HOLogic.dest_list
        val extr' = map (fn i => nth prog' (i-1)) range
      in HOLogic.mk_list (fastype_of prog |> dest_listT) extr' end
    | extract_range ctxt (Range2 (p1,r1,p2,r2)) = let
        val t1 = extract_range ctxt (Range (p1,r1))
        val t2 = extract_range ctxt (Range (p2,r2))
      in HOLogic.mk_prod (t1,t2) end

  val tilde = Parse.sym_ident :-- (fn "~" => Scan.succeed () | _ => Scan.fail) >> #1;
  val emptyset = Parse.sym_ident :-- (fn "\<emptyset>" => Scan.succeed () | _ => Scan.fail) >> #1;

  val index_list : int list parser =
    Parse.list1 Parse.nat || (emptyset >> K [])

  fun read_range (options:options) _ : range context_parser = 
    Scan.lift (index_list -- Scan.option (tilde |-- index_list))
      >> (fn (indices,NONE) => Range (get_current_program_name (#util_options options), indices)
           | (indices1,SOME indices2) => Range2 (the_left_program options, indices1, the_right_program options, indices2))

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
      let val (T1,T2) = dest_invariant2T "hoare_thm" (fastype_of pre)
          val prog12T = HOLogic.mk_prodT (programT T1, programT T2)
          val prog1 = Const(\<^const_name>\<open>fst\<close>, prog12T --> programT T1) $ prog
          val prog2 = Const(\<^const_name>\<open>snd\<close>, prog12T --> programT T2) $ prog
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
    val p12_p23 = Const(\<^const_name>\<open>append\<close>, progT --> progT --> progT) $ p12 $ p23
    (* p12@p23 \<equiv> p13 *)
    val p13_thm = append_conv (Thm.cterm_of ctxt p12_p23)
    val p13 = Thm.rhs_of p13_thm |> Thm.term_of
    val (range13,_,sorted_thm) = sort_program ctxt (range12@range23, p13)
    (* val _ = sorted_thm |> \<^print> *)
    val thm = @{thm join_hoare} OF [hoare_append, p13_thm, sorted_thm]
  in (Range (prog12,range13),thm) end


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

  val subgoal_tactics = [("wp_tac",wp_tac),("independence_tac",independence_tac)]

)

(* structure Logic2 = Hoare_Logic(
  val binding = \<^binding>\<open>tmp_hoare2\<close>

  type options = {left_memory_type: typ option, right_memory_type: typ option}
  val default_options = {left_memory_type = NONE, right_memory_type = NONE}
  fun set_left_memory_type T ({left_memory_type,right_memory_type}:options) : options = {left_memory_type = SOME T, right_memory_type = right_memory_type}
  fun set_right_memory_type T ({left_memory_type,right_memory_type}:options) : options = {right_memory_type = SOME T, left_memory_type = left_memory_type}
  fun set_option "left_memory" typ_str ctxt m = let
        val T = Syntax.read_typ ctxt typ_str
        val T = Morphism.typ m T
        in set_left_memory_type T end
    | set_option "right_memory" typ_str ctxt m = let
        val T = Syntax.read_typ ctxt typ_str
        val T = Morphism.typ m T
        in set_right_memory_type T end
    | set_option name _ _ _ = error ("Unknown option " ^ name)
    

  type range = int list * int list
  fun program_term_typ options = let
    val left = #left_memory_type options |> the' (fn _ => "Left memory type not set. Use \"Hoare config left_memory = <typ>\".")
    val right = #right_memory_type options |> the' (fn _ => "Right memory type not set. Use \"Hoare config right_memory = <typ>\".")
    in program2T left right end
  fun invariant_typ options = let
    val left = #left_memory_type options |> the' (fn _ => "Left memory type not set. Use \"Hoare config left_memory = <typ>\".")
    val right = #right_memory_type options |> the' (fn _ => "Right memory type not set. Use \"Hoare config right_memory = <typ>\".")
    in invariant2T left right end

  fun pretty_range _ (range1,range2) = 
    [Pretty.commas (range1 |> map (string_of_int #> Pretty.str)) |> Pretty.block,
     Pretty.str "~",
     Pretty.commas (range2 |> map (string_of_int #> Pretty.str)) |> Pretty.block]

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
 *)

end

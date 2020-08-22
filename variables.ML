structure Variables = struct

local
open Utils
in

fun zip a b = map2 (fn x => fn y => (x,y)) a b
fun zip3 a b c = map2 (fn x => fn (y,z) => (x,y,z)) a (zip b c)

fun dest_Abs_var (Const(\<^const_name>\<open>Abs_var\<close>,_) $ t) = t
  | dest_Abs_var t = raise TERM("dest_Abs_var", [t])

fun mk_varT memT valT = Type(\<^type_name>\<open>var\<close>, [memT,valT])

fun Abs_var_const memT valT = Const(\<^const_name>\<open>Abs_var\<close>, 
  HOLogic.mk_prodT (memT --> valT, valT --> memT --> memT)
    --> mk_varT memT valT)

val independence_add = Named_Theorems.add \<^named_theorems>\<open>independence\<close>

fun declare_variables (toolkit:'a toolkit) (decls:(binding*term*term) list) (st:'a) = let
  type decl = {binding:binding, getter:term, setter:term,
               def_thm:thm Unsynchronized.ref, valT:typ}
  val decls = Symtab.make (decls |> map (fn (b,g,s) => (Binding.name_of b,
    {binding=b, getter=g, setter=s, 
      valT = fastype_of g |> range_type,
      def_thm=Unsynchronized.ref @{thm asm_rl}, (* dummy thm *)
      valid_thm=Unsynchronized.ref @{thm asm_rl} (* dummy thm *)
      })))

  val memT = Symtab.get_first (fn (_,decl) => SOME (fastype_of (#getter decl) |> domain_type)) decls
    |> the' (fn _ => "declare_variables")

  (* Defining the variable: x = Abs_var (getter,setter) *)
  fun def decl st = let
    val x_def = Abs_var_const memT (#valT decl) $ HOLogic.mk_prod (#getter decl,#setter decl)
    val thm_binding = Binding.suffix_name "_def" (#binding decl)
    val (_,def_thm,st) = #define toolkit (#binding decl) thm_binding x_def st
    val _ = #def_thm decl := def_thm
  in st end
  val st = Symtab.fold (def o snd) decls st

  (* Goal term: valid_raw_var (UNIV,getter,setter) *)
  fun valid decl = let
    val tuple = HOLogic.mk_prod (HOLogic.mk_UNIV (#valT decl), HOLogic.mk_prod (#getter decl, #setter decl))
    val goal = Const(\<^const_name>\<open>valid_raw_var\<close>, fastype_of tuple --> HOLogic.boolT) $ tuple |> HOLogic.mk_Trueprop
  in goal end

  (* Keys and valid_goals are ordered the same way *)
  val (keys,valid_goals) = Symtab.dest decls |> map (fn (name,decl) => (name,valid decl)) |> split_list

  fun mk_pairs [] = []
    | mk_pairs (k::ks) = (map (fn l => (k,l)) ks) @ mk_pairs ks
  val pairs = mk_pairs keys
  fun independence_goal x y = let
    val xdecl = Symtab.lookup decls x |> the' (fn _ => "declare_variables")
    val ydecl = Symtab.lookup decls y |> the' (fn _ => "declare_variables")
    fun mk_all v T body = Logic.all_const T $ Abs(v,T,body)
    (* \<And>a b m. x_setter a (y_setter b m) = y_setter b (x_setter a m) *)
    val t = HOLogic.mk_eq (#setter xdecl $ Bound 2 $ (#setter ydecl $ Bound 1 $ Bound 0),
                           #setter ydecl $ Bound 1 $ (#setter xdecl $ Bound 2 $ Bound 0))
            |> HOLogic.mk_Trueprop
            |> mk_all "m" memT
            |> mk_all "b" (#valT ydecl)
            |> mk_all "a" (#valT xdecl)
  in t end
  val independence_goals = map (fn (x,y) => independence_goal x y) pairs

  (* Declaring derived theorems *)
  fun after_qed thms st : 'a = let
    val (valid_thms,independence_thms) = chop (length valid_goals) thms

    (* Putting the proven theorems into the decls-map *)
    val _ = map2 (fn key => fn valid_thm => 
        #valid_thm (Symtab.lookup decls key |> the) := valid_thm) keys valid_thms

    (* Declare the derived theorems for one variable *)
    fun process_decl (_,decl) st = let
      fun derive (name, rule) st = let
        val derived_thm = rule OF [!(#def_thm decl), !(#valid_thm decl)]
        val st = #note toolkit (Binding.qualify_name true (#binding decl) name) derived_thm st
        val st = #declaration toolkit (fn m => Thm.apply_attribute Simplifier.simp_add 
                        (Morphism.thm m derived_thm) #> snd) st
      in st end
      val st = fold derive
          [("valid", @{thm declare_variable_command_helper_valid}),
           ("eval", @{thm declare_variable_command_helper_eval}),
           ("update", @{thm declare_variable_command_helper_update})] st
    in st end
    val st = Symtab.fold process_decl decls st

    (* Create independence theorems *)
    fun independence (x,y) thm st = let
      fun derive (name, flip, indep_add, rule) st = let
        val xdecl = Symtab.lookup decls x |> the' (fn _ => "declare_variables")
        val ydecl = Symtab.lookup decls y |> the' (fn _ => "declare_variables")
        val derived_thm = rule OF [!(#def_thm xdecl), !(#def_thm ydecl)]
        val derived_thm = derived_thm OF [!(#valid_thm xdecl), !(#valid_thm ydecl), thm]
        val binding = if flip then Binding.qualify_name true (#binding ydecl) x
                              else Binding.qualify_name true (#binding xdecl) y
        val binding = Binding.qualify_name true binding name
        val st = #note toolkit binding derived_thm st
        val attrs = if indep_add then [Simplifier.simp_add, independence_add]
                                 else [Simplifier.simp_add]
        fun apply_attrs thm context = 
          fold (fn attr => fn (thm,context) => Thm.apply_attribute attr thm context) attrs (thm,context)
          |> snd
        val st = #declaration toolkit (fn m => apply_attrs (Morphism.thm m derived_thm)) st
      in st end
      val st = fold derive
          [("indep", false, true, @{thm declare_variable_command_helper_indep}),
           ("indep", true, true, @{thm declare_variable_command_helper_indep_flip}),
           ("indep'", false, false, @{thm declare_variable_command_helper_indep'}),
           ("indep'", true, false, @{thm declare_variable_command_helper_indep'_flip})] st
    in st end
    val st = fold2 independence pairs independence_thms st

  in st end

  (* Proving validity: valid_raw_var (UNIV,getter,setter) for each var *)
  val state = #theorems toolkit after_qed (valid_goals@independence_goals) st
  (* Tactic that applies valid_raw_varI' to the first |valid_goals| subgoals *)
  fun tac ctxt = 
    map_index (fn (i,_) => TRY (resolve_tac ctxt @{thms valid_raw_varI'} (i+1))) valid_goals |> rev |> EVERY
  val state = Proof.apply (Method.Basic (fn ctxt => SIMPLE_METHOD (tac ctxt)), Position.no_range) state
    |> ensure_result (fn _ => "Failed to apply rule valid_raw_varI'") |> Seq.hd
  in state end

fun declare_variables_command (toolkit:'a toolkit) (decls:(binding*string*string) list) (st:'a) = let
  val ctxt = #context toolkit st |> Context.proof_of

  val decls_raw = map (fn (b,g,s) => (b, Syntax.parse_term ctxt g, Syntax.parse_term ctxt s)) decls
  val idx = 1 + fold (fn (_,g,s) => fn i => Int.max (Int.max (maxidx_of_term g, maxidx_of_term s), i)) 
            decls_raw ~1
  val memT = TVar(("?'mem",idx),dummyS)
  fun constrain (b,g,s) = let
    val valT = TVar(("?'val_" ^ Binding.name_of b, idx), dummyS)
    val g = Type.constraint (memT --> valT) g
    val s = Type.constraint (valT --> memT --> memT) s
    in (b,g,s) end
  val decls_raw = map constrain decls_raw

  val bindings = map #1 decls_raw
  val getters = map #2 decls_raw
  val setters = map #3 decls_raw
  val (getters, setters) = Syntax.check_terms ctxt (getters@setters) |> chop (length getters)
  val decls = zip3 bindings getters setters

  val state = declare_variables toolkit decls st

in state end


val declare_variable_command_parser = 
  (Parse.binding -- (Parse.$$$ "get" |-- Parse.term) -- (Parse.$$$ "set" |-- Parse.term)
    >> (fn ((x,y),z) => (x,y,z)))
  |> Parse.and_list1

val _ = Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>declare_variables\<close> "Run a Hoare logic command (with proof obligation)"
  (declare_variable_command_parser >> (declare_variables_command lthy_toolkit))

(* TODO add an independence tactic *)

end

end
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

fun declare_variables (toolkit:'a toolkit) (decls:(binding*term*term) list) (st:'a) = let
  val ctxt = #context toolkit st |> Context.proof_of

  fun def (binding,getter,setter) st = let
    val (memT,valT) = fastype_of getter |> dest_funT
    val x_def = Abs_var_const memT valT $ HOLogic.mk_prod (getter,setter)
    (* Defining the variable: x = Abs_var (getter,setter) *)
    val thm_binding = Binding.suffix_name "_def" binding
    val (_,def_thm,st) = #define toolkit binding thm_binding x_def st

    (* Creating the validity proof goal term *)
    val valid_raw_goal = let val tuple = HOLogic.mk_prod (HOLogic.mk_UNIV valT, HOLogic.mk_prod (getter,setter))
      in Const(\<^const_name>\<open>valid_raw_var\<close>, fastype_of tuple --> HOLogic.boolT) $ tuple |> HOLogic.mk_Trueprop end
  in ((def_thm,valid_raw_goal),st) end

  (* Define all variables, creating all proof goals *)
  val (results, st) = fold_map def decls st
  val (def_thms, valid_raw_goals) = split_list results
  val bindings = map #1 decls
  val getters = map #2 decls
  val setters = map #3 decls

  (* Declaring derived theorems (and adding to simplifier) *)
  fun after_qed valid_thms st : 'a = let
    fun derive' (binding,def_thm,valid_thm) (name, rule) st = let
      val derived_thm = rule OF [def_thm, valid_thm]
      val st = #note toolkit (Binding.qualify_name true binding name) derived_thm st
      val st = #declaration toolkit (fn m => Thm.apply_attribute Simplifier.simp_add 
                      (Morphism.thm m derived_thm) #> snd) st
    in st end
    fun derive x st = fold (derive' x)
        [("valid", @{thm declare_variable_command_helper_valid}),
         ("eval", @{thm declare_variable_command_helper_eval}),
         ("update", @{thm declare_variable_command_helper_update})] st
    val st = fold derive (zip3 bindings def_thms valid_thms) st
  in st end

  (* Proving validity: valid_raw_var (UNIV,getter,setter) for each var *)
  val state = #theorems toolkit after_qed valid_raw_goals st
  fun valid_raw_tac ctxt = ALLGOALS (resolve_tac ctxt @{thms valid_raw_varI'})
  val state = Proof.apply (Method.Basic (fn ctxt => SIMPLE_METHOD (valid_raw_tac ctxt)), Position.no_range) state
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

val _ = Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>declare_variable\<close> "Run a Hoare logic command (with proof obligation)"
  (declare_variable_command_parser >> (declare_variables_command lthy_toolkit))

(* TODO add an independence tactic *)

end

end
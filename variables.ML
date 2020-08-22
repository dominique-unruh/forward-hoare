structure Variables = struct

local
open Utils
in

fun dest_Abs_var (Const(\<^const_name>\<open>Abs_var\<close>,_) $ t) = t
  | dest_Abs_var t = raise TERM("dest_Abs_var", [t])

val declare_variable_command_parser = 
  Parse.binding -- (Parse.$$$ "get" |-- Parse.term) -- (Parse.$$$ "set" |-- Parse.term)

fun declare_variable_command (toolkit:'a toolkit) binding getter_str setter_str (st:'a) = let
  val ctxt = #context toolkit st |> Context.proof_of

  (* Parsing getter,setter *)
  val getter_raw_term = Syntax.parse_term ctxt getter_str
  val setter_raw_term = Syntax.parse_term ctxt setter_str
  val x_def_raw_term = @{const Abs_var(_,_)} $ HOLogic.mk_prod (getter_raw_term,setter_raw_term)
  val x_def = Syntax.check_term ctxt x_def_raw_term |> \<^print>

  val (getter, setter) = dest_Abs_var x_def |> HOLogic.dest_prod
  val (_,valT) = fastype_of getter |> dest_funT

  (* Defining the variable: x = Abs_var (getter,setter) *)
  val thm_binding = Binding.suffix_name "_def" binding
  val (_,def_thm,st) = #define toolkit binding thm_binding x_def st

  (* Declaring derived theorems (and adding to simplifier) *)
  fun after_qed thm st : 'a = let
    fun derive (name, rule) st = let
      val derived_thm = rule OF [def_thm, thm]
      val st = #note toolkit (Binding.qualify_name true binding name) derived_thm st
      val st = #declaration toolkit (fn m => Thm.apply_attribute Simplifier.simp_add 
                      (Morphism.thm m derived_thm) #> snd) st
    in st end
    val st = fold derive [("valid", @{thm declare_variable_command_helper_valid}),
                          ("eval", @{thm declare_variable_command_helper_eval}),
                          ("update", @{thm declare_variable_command_helper_update})] st
  in st end

  (* Proving validity: valid_raw_var (UNIV,getter,setter) *)
  val valid_raw_goal = let val tuple = HOLogic.mk_prod (HOLogic.mk_UNIV valT, HOLogic.mk_prod (getter,setter))
    in Const(\<^const_name>\<open>valid_raw_var\<close>, fastype_of tuple --> HOLogic.boolT) $ tuple |> HOLogic.mk_Trueprop end
  val state = #theorem toolkit after_qed valid_raw_goal st
  fun valid_raw_tac ctxt = resolve_tac ctxt @{thms valid_raw_varI'} 1
  val state = Proof.apply (Method.Basic (fn ctxt => SIMPLE_METHOD (valid_raw_tac ctxt)), Position.no_range) state
    |> ensure_result (fn _ => "Failed to apply rule valid_raw_varI'") |> Seq.hd
  in state end

val _ = Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>declare_variable\<close> "Run a Hoare logic command (with proof obligation)"
  (declare_variable_command_parser >> (fn ((x,get),set) => 
    declare_variable_command lthy_toolkit x get set))

(* TODO add an independence tactic *)

end

end
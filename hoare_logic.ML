signature HOARE_LOGIC_ARGS =
sig
(* type program *)
type range
type options
val binding: binding
val program_term_typ: options -> typ
val invariant_typ: options -> typ
(* Can assume that term is of type program_term_typ *)
val check_program: Proof.context -> term -> unit
(* Can assume that term is of type invariant_typ *)
val check_invariant: Proof.context -> term -> unit
(* val read_program: Proof.context -> string -> program *)
val read_range: options -> range option -> range context_parser
val pretty_range: Proof.context -> range -> Pretty.T
(* val read_invariant: Proof.context -> string -> term *)
val postcondition_generators: (term->term->term*(Proof.context->tactic)) context_parser Symtab.table
(* join_hoare ctxt invariant1 range12 invariant2 range23 invariant3 thm12 thm23 *)
val join_hoare: Proof.context -> term -> range -> term -> range -> term -> thm -> thm -> (range*thm)
(* valid_range program range *)
(* val valid_range: term -> range -> bool *)
(* extract_range range
Contract: return value must not change
 *)
val extract_range: Proof.context -> range -> term
(* hoare_thm pre prog post *)
val hoare_thm: Proof.context -> term -> term -> term -> term
val invariant_implication: Proof.context -> term -> term -> term
val default_options: options
(* set_option name content ctxt m options *)
val set_option: string -> string -> Proof.context -> morphism -> options -> options
end

signature HOARE_LOGIC =
sig
type program
type range
val logic: Forward_Hoare.logic
(* val ex_program : program -> Forward_Hoare.ex_program
val program_ex : Forward_Hoare.ex_program -> program *)
val ex_range : range -> Forward_Hoare.ex_range
val range_ex : Forward_Hoare.ex_range -> range
end


functor Hoare_Logic(Logic: HOARE_LOGIC_ARGS): HOARE_LOGIC =
struct

open Forward_Hoare

(* type program = Logic.program *)
type range = Logic.range
type options = Logic.options
(* exception Program of program *)
exception Range of range
exception Options of options

fun err str = error (Binding.name_of Logic.binding ^ "." ^ str)

(* fun read_program ctxt str = Ex_Program (Program (Logic.read_program ctxt str)) *)
(* fun ex_program prog = Ex_Program (Program prog)
fun program_ex (Ex_Program (Program prog)) = prog
  | program_ex (Ex_Program e) = err ("program_ex: " ^ \<^make_string> e) *)

fun ex_range range = Ex_Range (Range range)
fun range_ex (Ex_Range (Range prog)) = prog
  | range_ex (Ex_Range e) = err ("range_ex: " ^ \<^make_string> e)

fun ex_options options = Ex_Options (Options options)
fun options_ex (Ex_Options (Options options)) = options
  | options_ex (Ex_Options e) = err ("options_ex: " ^ \<^make_string> e)

fun read_range options relative = 
  Logic.read_range (options_ex options) (Option.map range_ex relative) >> ex_range

fun pretty_range ctxt range = Logic.pretty_range ctxt (range_ex range)

(* fun valid_range prog range = Logic.valid_range prog (range_ex range) *)
fun extract_range ctxt range = let
  val fragment = Logic.extract_range ctxt (range_ex range)
  val _ = catch_internal_error Logic.binding "typechecking result of extract_range" (Sign.cert_term (Proof_Context.theory_of ctxt)) fragment
  in fragment end

fun join_hoare ctxt a r1 b r2 c h1 h2 = Logic.join_hoare ctxt a (range_ex r1) b (range_ex r2) c h1 h2
  |> apfst ex_range

fun hoare_thm ctxt pre prog post = let
  val term = Logic.hoare_thm ctxt pre prog post
  val _ = catch_internal_error Logic.binding "typechecking result of hoare_thm" (Sign.cert_prop (Proof_Context.theory_of ctxt)) term
  in term end

fun invariant_implication ctxt a b = let
  val term = Logic.invariant_implication ctxt a b
  val _ = catch_internal_error Logic.binding "typechecking result of invariant_implication" (Sign.cert_prop (Proof_Context.theory_of ctxt)) term
  in term end

val default_options = ex_options Logic.default_options

fun set_option name content ctxt m options = 
  ex_options (Logic.set_option name content ctxt m (options_ex options))

fun program_term_typ options = Logic.program_term_typ (options_ex options)

fun invariant_typ options = Logic.invariant_typ (options_ex options)

(* fun program_morphism m prog = ex_program (Logic.program_morphism m (program_ex prog)) *)

val logic : logic = {
  serial = serial(),
  binding = Logic.binding,
  program_term_typ = program_term_typ,
  invariant_typ = invariant_typ,
  check_program = Logic.check_program,
  check_invariant = Logic.check_invariant,
  (* read_program = read_program, *)
  read_range = read_range,
  pretty_range = pretty_range,
  extract_range = extract_range,
  (* valid_range = valid_range, *)
  hoare_thm = hoare_thm,
  (* read_invariant = Logic.read_invariant, *)
  join_hoare = join_hoare,
  postcondition_generators = Logic.postcondition_generators,
  invariant_implication = invariant_implication,
  default_options = default_options,
  set_option = set_option
  (* program_morphism = program_morphism *)
}

val _ = Context.>> (Context.map_theory (Logic_Data.map (Symtab.update_new (Binding.name_of Logic.binding, logic))))
end

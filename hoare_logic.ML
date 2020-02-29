signature HOARE_LOGIC_ARGS =
sig
(* type program *)
type range
val binding: binding
val program_term_typ: typ
val check_program: Proof.context -> term -> unit
(* val read_program: Proof.context -> string -> program *)
val read_range: range option -> range context_parser
val pretty_range: Proof.context -> range -> Pretty.T
val read_invariant: Proof.context -> string -> term
val postcondition_generators: (term->term->term*(Proof.context->tactic)) context_parser Symtab.table
(* join_hoare ctxt program invariant1 range12 invariant2 range23 invariant3 thm12 thm23 *)
val join_hoare: Proof.context -> term -> term -> range -> term -> range -> term -> thm -> thm -> (range*thm)
(* valid_range program range *)
val valid_range: term -> range -> bool
(* extract_range program range
Contract: valid range *)
val extract_range: term -> range -> term
val hoare_thm: Proof.context -> term -> term -> term -> term (* pre prog post *)
val invariant_implication: Proof.context -> term -> term -> term
(* val program_morphism: morphism -> program -> program *)
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
exception Program of program
exception Range of range

fun err str = error (Binding.name_of Logic.binding ^ "." ^ str)

(* fun read_program ctxt str = Ex_Program (Program (Logic.read_program ctxt str)) *)
(* fun ex_program prog = Ex_Program (Program prog)
fun program_ex (Ex_Program (Program prog)) = prog
  | program_ex (Ex_Program e) = err ("program_ex: " ^ \<^make_string> e) *)

fun ex_range range = Ex_Range (Range range)
fun range_ex (Ex_Range (Range prog)) = prog
  | range_ex (Ex_Range e) = err ("range_ex: " ^ \<^make_string> e)

fun read_range relative = 
  Logic.read_range (Option.map range_ex relative) >> ex_range

fun pretty_range ctxt range = Logic.pretty_range ctxt (range_ex range)

fun valid_range prog range = Logic.valid_range prog (range_ex range)
fun extract_range prog range = Logic.extract_range prog (range_ex range)
fun join_hoare ctxt prog a r1 b r2 c h1 h2 = Logic.join_hoare ctxt prog a (range_ex r1) b (range_ex r2) c h1 h2
  |> apfst ex_range

(* fun program_morphism m prog = ex_program (Logic.program_morphism m (program_ex prog)) *)

val logic : logic = {
  serial = serial(),
  binding = Logic.binding,
  program_term_typ = Logic.program_term_typ,
  check_program = Logic.check_program,
  (* read_program = read_program, *)
  read_range = read_range,
  pretty_range = pretty_range,
  extract_range = extract_range,
  valid_range = valid_range,
  hoare_thm = Logic.hoare_thm,
  read_invariant = Logic.read_invariant,
  join_hoare = join_hoare,
  postcondition_generators = Logic.postcondition_generators,
  invariant_implication = Logic.invariant_implication
  (* program_morphism = program_morphism *)
}

val _ = Context.>> (Context.map_theory (Logic_Data.map (Symtab.update_new (Binding.name_of Logic.binding, logic))))
end

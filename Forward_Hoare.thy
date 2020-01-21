theory Forward_Hoare
  imports "HOL-Library.Rewrite" "HOL-Eisbach.Eisbach" Main
  keywords "do" :: prf_decl % "proof"
    and "do_prf" :: prf_goal % "proof"
begin

ML \<open>
signature HOARE_LOGIC_ARGS =
sig
type program
type range
val binding: binding
val read_program: Proof.context -> string -> program
val read_range: Proof.context -> string -> range
val valid_range: program -> range -> bool
(* Contract: valid range *)
val extract_range: program -> range -> term
val hoare_thm : Proof.context -> term -> term -> term -> term (* pre prog post *)
end

datatype ex_program = Ex_Program of exn
datatype ex_range = Ex_Range of exn

type logic = {
  binding: binding,
  serial: serial,
  read_program: Proof.context -> string -> ex_program,
  read_range: Proof.context -> string -> ex_range,
  valid_range: ex_program -> ex_range -> bool,
  extract_range: ex_program -> ex_range -> term,
  hoare_thm: Proof.context -> term -> term -> term -> term
}

structure Logic_Data = Theory_Data(
  type T = logic Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (fn (x,y) => #serial x = #serial y)
  val extend = I
)

signature HOARE_LOGIC =
sig
type program
type range
val logic: logic
val ex_program : program -> ex_program
val program_ex : ex_program -> program
val ex_range : range -> ex_range
val range_ex : ex_range -> range
end

functor Hoare_Logic(Logic: HOARE_LOGIC_ARGS): HOARE_LOGIC =
struct

type program = Logic.program
type range = Logic.range
exception Program of program
exception Range of range

fun err str = error (Binding.name_of Logic.binding ^ "." ^ str)

fun read_program ctxt str = Ex_Program (Program (Logic.read_program ctxt str))
fun ex_program prog = Ex_Program (Program prog)
fun program_ex (Ex_Program (Program prog)) = prog
  | program_ex (Ex_Program e) = err ("program_ex: " ^ \<^make_string> e)

fun read_range ctxt str = Ex_Range (Range (Logic.read_range ctxt str))
fun ex_range prog = Ex_Range (Range prog)
fun range_ex (Ex_Range (Range prog)) = prog
  | range_ex (Ex_Range e) = err ("range_ex: " ^ \<^make_string> e)

fun valid_range prog range = Logic.valid_range (program_ex prog) (range_ex range)
fun extract_range prog range = Logic.extract_range (program_ex prog) (range_ex range)

val logic : logic = {
  serial = serial(),
  binding = Logic.binding,
  read_program = read_program,
  read_range = read_range,
  extract_range = extract_range,
  valid_range = valid_range,
  hoare_thm = Logic.hoare_thm
}

val _ = Context.>> (Context.map_theory (Logic_Data.map (Symtab.update_new (Binding.name_of Logic.binding, logic))))
end

fun get_logic thy name = Symtab.lookup (Logic_Data.get thy) name
fun get_logic' ctxt = get_logic (Proof_Context.theory_of ctxt)
\<close>

ML \<open>
fun def' binding t lthy =
  let val ((const,_),lthy) = Local_Theory.define ((binding,NoSyn),((Binding.suffix_name "_def" binding,[]),t)) lthy
  in (const,lthy) end
fun def binding t lthy = def' binding t lthy |> snd
\<close>

type_synonym var = String.literal
type_synonym mem = \<open>var \<Rightarrow> int\<close>
datatype instruction = Add var var | Set var int | Guess var
type_synonym program = "instruction list"

ML \<open>
type var = string
type program = { binding: binding, code: ex_program, logic: string }
(* fun program_to_cterm ctxt p = program_to_term p |> Thm.cterm_of ctxt *)
\<close>


ML \<open>
type invariant = {
  binding: binding,
  term: term,
  const: term
}
\<close>


ML \<open>
type hoare = {
  binding: binding,
  range: ex_range,
  program: string,
  program_fragment_const: term,
  precondition: string,
  postcondition: string,
  valid: thm
}
\<close>

ML \<open>
structure Hoare_Data = Proof_Data (
  type T = { invariants: invariant Symtab.table,
             hoares: hoare Symtab.table,
             programs: program Symtab.table,
             current_program: string option
  }
  fun init _ = { invariants=Symtab.empty, hoares=Symtab.empty,
    programs=Symtab.empty, current_program=NONE }
)
\<close>


ML \<open>
fun mk_the t = let val oT = fastype_of t in case oT of 
  Type(\<^type_name>\<open>option\<close>,[T]) => Const(\<^const_name>\<open>the\<close>, oT --> T) $ t
 | _ => raise TYPE("mk_the: expected option type",[oT],[t]) end
\<close>

ML \<open>
fun map_invariants f = Hoare_Data.map (fn {invariants,hoares,programs,current_program} => 
  {invariants=f invariants, hoares=hoares, programs=programs, current_program=current_program})
fun map_hoares f = Hoare_Data.map (fn {invariants,hoares,programs,current_program} => 
  {invariants=invariants, hoares=f hoares, programs=programs, current_program=current_program})
fun map_programs f = Hoare_Data.map (fn {invariants,hoares,programs,current_program} => 
  {invariants=invariants, hoares=hoares, programs=f programs, current_program=current_program})
fun set_current_program name = Hoare_Data.map (fn {invariants,hoares,programs,current_program=_} => 
  {invariants=invariants, hoares=hoares, programs=programs, current_program=SOME name})
fun add_invariant0 i = map_invariants (Symtab.update_new (Binding.name_of (#binding i), i))
fun add_hoare0 i = map_hoares (Symtab.update_new (Binding.name_of (#binding i), i))
fun add_program0 p ctxt = let
  val name = Binding.name_of (#binding p)
  val ctxt = map_programs (Symtab.update_new (name, p)) ctxt
  val ctxt = set_current_program name ctxt
  in ctxt end
fun get_invariant ctxt name = Symtab.lookup (Hoare_Data.get ctxt |> #invariants) name
fun get_hoare ctxt name = Symtab.lookup (Hoare_Data.get ctxt |> #hoares) name
fun get_program ctxt name = Symtab.lookup (Hoare_Data.get ctxt |> #programs) name
fun get_current_program ctxt = Hoare_Data.get ctxt |> #current_program
\<close>

ML \<open>
fun add_invariant binding (invariant:term) ctxt : invariant * Proof.context = let
  fun bind suffix = Binding.suffix_name suffix binding
  val _ = tracing ("Adding invariant "^ Pretty.string_of (Binding.pretty binding) ^ ": " ^ Syntax.string_of_term ctxt invariant)
  val (invariant_const,ctxt) = def' (bind "_inv") invariant ctxt
  val info : invariant = {binding=binding, const=invariant_const, term=invariant}
  val ctxt = add_invariant0 info ctxt
  in (info,ctxt) end
\<close>

ML \<open>
fun add_hoare1 binding (program:program) range (precondition:invariant) (postcondition:invariant) (ctxt:Proof.context) = let
  fun bind suffix = Binding.suffix_name suffix binding
  val logic = get_logic (Proof_Context.theory_of ctxt) (#logic program) |> the
  val program_fragment = (#extract_range logic) (#code program) range
  (* val program_fragment_ct = program_to_term program_fragment *)
  val _ = tracing ("Program fragment: " ^ Syntax.string_of_term ctxt program_fragment)
  val (program_fragment_const,ctxt) = 
      def' (bind "_prog") program_fragment ctxt
  val info : hoare = {binding=binding, range=range,
    precondition=Binding.name_of (#binding precondition),
    postcondition=Binding.name_of (#binding postcondition),
    program_fragment_const=program_fragment_const,
    program=program |> #binding |> Binding.name_of,
    valid= @{thm TrueI}
  }
  (* val ctxt = add_hoare0 info ctxt *)
  in (info,ctxt) end
\<close>


section \<open>Experiments\<close>

ML \<open>
structure Do_Prf = Proof_Data(
  type T = Proof.state -> Proof.state
  fun init _ = fn _ => error "don't call this"
)
\<close>

ML \<open>
fun do_prf_cmd source state = let
  val expr = ML_Context.expression (Input.pos_of source) 
    (ML_Lex.read "Context.>> (Context.map_proof (Do_Prf.put (" @ ML_Lex.read_source source @ ML_Lex.read ")))")
  val f = Context.proof_map expr (Proof.context_of state) |> Do_Prf.get
  val state = f state
  in state end

fun do_cmd source = let
  val expr = ML_Context.expression (Input.pos_of source) (ML_Lex.read "Theory.local_setup (" @ ML_Lex.read_source source @ ML_Lex.read ")")  
  in Context.proof_map expr |> Proof.map_context end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>do\<close> "do something to the context in a proof"
    (Parse.ML_source >> (Toplevel.proof o do_cmd));
  Outer_Syntax.command \<^command_keyword>\<open>do_prf\<close> "do something to the context in a proof"
    (Parse.ML_source >> (Toplevel.proof o do_prf_cmd));
\<close>

ML \<open>
  fun prove binding after_qed prop state = 
Proof.have true NONE after_qed [] [] [((binding,[]),[(prop,[])])] true state |> \<^print> |> snd
\<close>

ML \<open>

fun hoare_thm ctxt (hoare:hoare) : cterm = let
  val logic = hoare |> #program |> get_program ctxt |> the |> #logic |> get_logic' ctxt |> the
  val pre = #precondition hoare |> get_invariant ctxt |> the |> #const
  val post = #postcondition hoare |> get_invariant ctxt |> the |> #const
  val prog = #program_fragment_const hoare
  val prop = #hoare_thm logic ctxt pre prog post
  in Thm.cterm_of ctxt prop end
\<close>

ML \<open>
fun update_hoare_valid new_valid ({binding, range, program_fragment_const, precondition,
  postcondition, program, valid=_}:hoare) : hoare =
   {binding=binding, range=range, 
    program_fragment_const=program_fragment_const, precondition=precondition,
    postcondition=postcondition,
    program=program,
    valid=new_valid}
\<close>


ML \<open>
fun add_hoare2 binding (program:program) range (precondition:invariant) (postcondition:invariant) state : hoare * Proof.state = let
  val (info,state) = Proof.map_context_result (add_hoare1 binding program range precondition postcondition) state
  fun after_qed (_,[[valid]]) = Proof.map_context (add_hoare0 (update_hoare_valid valid info))
  val valid_prop = hoare_thm (Proof.context_of state) info |> Thm.term_of
  val state = prove (Binding.suffix_name "_valid" binding) after_qed valid_prop state
  in (info,state) end
\<close>


ML \<open>
fun add_hoare3 binding (program:string option) range (precondition:string) (postcondition:term) state = let
    val ctxt = Proof.context_of state
    val program = case program of 
      SOME program => program
    | NONE => get_current_program ctxt |> the
    val program = get_program ctxt program |> the
    val precondition = case get_invariant (Proof.context_of state) precondition of
      SOME inv => inv | NONE => error ("Undefined precondition " ^ precondition)
    val (postcondition,state) = Proof.map_context_result (add_invariant binding postcondition) state
    val (_,state) = add_hoare2 binding program range precondition postcondition state
in state end
\<close>


end

signature HOARE_LOGIC_ARGS =
sig
type program
type range
val binding: binding
val read_program: Proof.context -> string -> program
val read_range: Proof.context -> string -> range
val read_invariant: Proof.context -> string -> term
val join_hoare: Proof.context -> program -> term -> range -> term -> range -> term -> thm -> thm -> (range*thm)
val valid_range: program -> range -> bool
(* Contract: valid range *)
val extract_range: program -> range -> term
val hoare_thm : Proof.context -> term -> term -> term -> term (* pre prog post *)
end

structure Forward_Hoare =
struct

fun string_of_binding kind binding = let
  val name = Binding.name_of binding
  val props = Markup.properties (Position.def_properties_of (Binding.pos_of binding)) (Markup.entity kind name)
  val string = Markup.markup props name
in string end
val string_of_binding_program = string_of_binding "program"
val string_of_binding_invariant = string_of_binding "invariant"
val string_of_binding_logic = string_of_binding "hoare logic"
val string_of_binding_const = string_of_binding Markup.constantN


datatype ex_program = Ex_Program of exn
datatype ex_range = Ex_Range of exn

type logic = {
  binding: binding,
  serial: serial,
  read_program: Proof.context -> string -> ex_program,
  read_range: Proof.context -> string -> ex_range,
  read_invariant: Proof.context -> string -> term,
  valid_range: ex_program -> ex_range -> bool,
  extract_range: ex_program -> ex_range -> term, (* TODO do we need that? *)
  hoare_thm: Proof.context -> term -> term -> term -> term,
  (* join_hoare ctxt prog a r1 b r2 c h1 h2
     returns thm {a}r1;r2{c} *)
  join_hoare: Proof.context -> ex_program -> term -> ex_range -> term -> ex_range -> term -> thm -> thm -> (ex_range*thm)
}

structure Logic_Data = Theory_Data(
  type T = logic Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (fn (x,y) => #serial x = #serial y)
  val extend = I
)



fun get_logic thy name = Symtab.lookup (Logic_Data.get thy) name
fun get_logic' ctxt = get_logic (Proof_Context.theory_of ctxt)

fun def' binding t lthy =
  let val thm_binding = Binding.suffix_name "_def" binding
      val ((const,_),lthy) = Local_Theory.define ((binding,NoSyn),((thm_binding,[]),t)) lthy
      val _ = tracing ("Defining " ^ string_of_binding_const binding ^ " := " ^ Syntax.string_of_term lthy t)
  in (const,lthy) end
(* fun def binding t lthy = def' binding t lthy |> snd *)
fun def'' binding t = Proof.map_context_result (def' binding t)

type var = string
type program = { binding: binding, code: ex_program, logic: string }

type invariant = {
  binding: binding,
  term: term,
  const: term
}

type hoare = {
  binding: binding,
  range: ex_range,
  program: string,
  program_fragment_const: term,
  precondition: string,
  postcondition: string,
  valid: thm
}

structure Hoare_Data = Proof_Data (
  type T = { invariants: invariant Symtab.table,
             hoares: hoare Symtab.table,
             programs: program Symtab.table,
             current_program: string option
  }
  fun init _ = { invariants=Symtab.empty, hoares=Symtab.empty,
    programs=Symtab.empty, current_program=NONE }
)

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

fun add_invariant binding (invariant:term) ctxt : invariant * Proof.context = let
  fun bind suffix = Binding.suffix_name suffix binding
  val (invariant_const,ctxt) = def' (bind "_inv") invariant ctxt
  val info : invariant = {binding=binding, const=invariant_const, term=invariant}
  val ctxt = add_invariant0 info ctxt
  in (info,ctxt) end

(* fun add_hoare_invalid binding (program:program) range (precondition:invariant) (postcondition:invariant) (ctxt:Proof.context) = let
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
    valid= @{thm Pure.asm_rl}
  }
  in (info,ctxt) end *)

structure Do_Prf = Proof_Data(
  type T = Proof.state -> Proof.state
  fun init _ = fn _ => error "don't call this"
)

fun do_prf_cmd source state = let
  val expr = ML_Context.expression (Input.pos_of source) 
    (ML_Lex.read "Context.>> (Context.map_proof (Forward_Hoare.Do_Prf.put (" @ ML_Lex.read_source source @ ML_Lex.read ")))")
  val f = Context.proof_map expr (Proof.context_of state) |> Do_Prf.get
  val state = f state
  in state end

fun do_cmd source = let
  val expr = ML_Context.expression (Input.pos_of source) (ML_Lex.read "Theory.local_setup (" @ ML_Lex.read_source source @ ML_Lex.read ")")  
  in Context.proof_map expr |> Proof.map_context end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>do\<close> "do something to the context in a proof"
    (Parse.ML_source >> (Toplevel.proof o do_cmd))
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>do_prf\<close> "do something to the context in a proof"
    (Parse.ML_source >> (Toplevel.proof o do_prf_cmd));

fun prove binding after_qed prop state = 
  Proof.have true NONE after_qed [] [] [((binding,[]),[(prop,[])])] true state |> snd

(* fun hoare_thm ctxt (hoare:hoare) : cterm = let
  val logic = hoare |> #program |> get_program ctxt |> the |> #logic |> get_logic' ctxt |> the
  val pre = #precondition hoare |> get_invariant ctxt |> the |> #const
  val post = #postcondition hoare |> get_invariant ctxt |> the |> #const
  val prog = #program_fragment_const hoare
  val prop = #hoare_thm logic ctxt pre prog post
  in Thm.cterm_of ctxt prop end *)

(* fun update_hoare_valid new_valid ({binding, range, program_fragment_const, precondition,
  postcondition, program, valid=_}:hoare) : hoare =
   {binding=binding, range=range, 
    program_fragment_const=program_fragment_const, precondition=precondition,
    postcondition=postcondition,
    program=program,
    valid=new_valid} *)

(* fun add_hoare2 binding after_qed0 (program:program) range (precondition:invariant) (postcondition:invariant) state : hoare * Proof.state = let
  fun bind suffix = Binding.suffix_name suffix binding
  val logic = get_logic (Proof.theory_of state) (#logic program) |> the
  val program_fragment = (#extract_range logic) (#code program) range
  val _ = tracing ("Program fragment: " ^ Syntax.string_of_term (Proof.context_of state) program_fragment)
  val (program_fragment_const,state) = 
      def'' (bind "_prog") program_fragment state
  val info : hoare = {binding=binding, range=range,
    precondition=Binding.name_of (#binding precondition),
    postcondition=Binding.name_of (#binding postcondition),
    program_fragment_const=program_fragment_const,
    program=program |> #binding |> Binding.name_of,
    valid= @{thm Pure.asm_rl} (* Arbitrary theorem here *)
  }
  (* val (info,state) = Proof.map_context_result (add_hoare_invalid binding program range precondition postcondition) state *)
  fun after_qed (_,validss) = case validss of [[valid]] =>
        after_qed0 (Proof.map_context (add_hoare0 (update_hoare_valid valid info)), valid)
    | _ => raise Match
  val valid_prop = hoare_thm (Proof.context_of state) info |> Thm.term_of
  val state = prove (Binding.suffix_name "_valid" binding) after_qed valid_prop state
  in (info,state) end *)

fun new_hoare binding after_qed0 (program:string) range (precondition:string) (postcondition:string) state = let
  val ctxt = Proof.context_of state
(*   val program = case program of 
    SOME program => program
  | NONE => get_current_program ctxt |> the *)
  val program = get_program ctxt program |> the
  val precondition = case get_invariant ctxt precondition of
    SOME inv => inv | NONE => error ("Undefined precondition " ^ precondition)
  val postcondition = case get_invariant ctxt postcondition of
    SOME inv => inv | NONE => error ("Undefined postcondition " ^ postcondition)
  (* val (postcondition,state) = Proof.map_context_result (add_invariant binding postcondition) state *)
  (* val (_,state) = add_hoare2 binding after_qed0 program range precondition postcondition state *)
  fun bind suffix = Binding.suffix_name suffix binding
  val logic = get_logic (Proof.theory_of state) (#logic program) |> the
  val program_fragment = (#extract_range logic) (#code program) range
  val _ = tracing ("Program fragment: " ^ Syntax.string_of_term (Proof.context_of state) program_fragment)
  val (program_fragment_const,state) = 
      def'' (bind "_prog") program_fragment state
  val valid_prop = #hoare_thm logic ctxt (#const precondition) program_fragment (#const postcondition)
  fun after_qed (_,validss) state = case validss of [[valid]] => let
      val info : hoare = {binding=binding, range=range,
        precondition=Binding.name_of (#binding precondition),
        postcondition=Binding.name_of (#binding postcondition),
        program_fragment_const=program_fragment_const,
        program=program |> #binding |> Binding.name_of,
        valid=valid}
      val state = Proof.map_context (add_hoare0 info) state
      in after_qed0 (state, info) end
    | _ => raise Match
  val state = prove (Binding.suffix_name "_valid" binding) after_qed valid_prop state

in state end

fun join_hoare binding (hoare1:string) (hoare2:string) state = let
  val ctxt = Proof.context_of state
  val hoare1' = get_hoare ctxt hoare1 |> the
  val hoare2' = get_hoare ctxt hoare2 |> the
  val program = #program hoare1'
  val _ = if #program hoare1' <> #program hoare2' then error "mismatch" else ()
  val _ = if #postcondition hoare1' <> #precondition hoare2' then error "mismatch" else ()
  val program' = program |> get_program ctxt |> the
  val logic = program' |> #logic |> get_logic' ctxt |> the
  val a = hoare1' |> #precondition |> get_invariant ctxt |> the |> #const
  val b = hoare1' |> #postcondition |> get_invariant ctxt |> the |> #const
  val c = hoare2' |> #postcondition |> get_invariant ctxt |> the |> #const
  val (range,joined_thm) = #join_hoare logic ctxt (#code program') a (#range hoare1') b (#range hoare2') c
          (#valid hoare1') (#valid hoare2')
  val program_fragment = (#extract_range logic) (#code program') range
  val (program_fragment_const,state) = 
      def'' (Binding.suffix_name "_prog" binding) program_fragment state

  val state = Proof.map_context (snd o Local_Theory.note ((Binding.suffix_name "_valid" binding, []), [joined_thm])) state

  val info : hoare = {binding=binding, range=range,
    precondition= #precondition hoare1',
    postcondition= #postcondition hoare2',
    program_fragment_const=program_fragment_const,
    program=program,
    valid=joined_thm
  }
  
  val state = Proof.map_context (add_hoare0 info) state

  in (state,info) end

fun extend_hoare binding (previous:string) after_qed0 range (postcondition:string) state = let
  val ctxt = Proof.context_of state
  val binding_step = Binding.suffix_name "_step" binding
  val previous_hoare = get_hoare ctxt previous |> the
  val program = #program previous_hoare
  val precondition = #postcondition previous_hoare
  fun after_qed (state, hoare) = let
    val (state, joined_hoare) = join_hoare binding previous (Binding.name_of binding_step) state
    in after_qed0 (state, hoare, joined_hoare) end
  val state = new_hoare binding_step after_qed program range precondition postcondition state
in state end

fun define_program_command logic binding content (ctxt:Proof.context) : Proof.context = let
  val logic' = get_logic' ctxt logic |> the
  val program = #read_program logic' ctxt content
  val ctxt = add_program0 {binding=binding, logic=logic, code=program} ctxt
in ctxt end

val _ = let
  val logic_parser = Parse.$$$ "(" |-- Parse.name --| Parse.$$$ ")"
  val name_parser = Parse.binding --| Parse.$$$ ":"
  val content_parser = Parse.embedded
  val parser = logic_parser -- name_parser -- content_parser
in
  Outer_Syntax.command \<^command_keyword>\<open>program\<close> "Declare a program"
    (parser >> (fn ((logic,name),content) => Toplevel.proof (Proof.map_context (define_program_command logic name content))))
end

fun define_invariant_command logic name content ctxt = let 
  val logic = get_logic' ctxt logic |> the
  val term = #read_invariant logic ctxt content
  val _ = tracing ("Declaring invariant "^ string_of_binding_invariant name ^ " in logic " ^ string_of_binding_logic (#binding logic))
  val (_,ctxt) = add_invariant name term ctxt
in ctxt end

val _ = let
  val logic_parser = Parse.$$$ "(" |-- Parse.name --| Parse.$$$ ")"
  val name_parser = Parse.binding --| Parse.$$$ ":"
  val content_parser = Parse.embedded
  val parser = logic_parser -- name_parser -- content_parser
in
  Outer_Syntax.command \<^command_keyword>\<open>invariant\<close> "Declare a program"
    (parser >> (fn ((logic,name),content) => Toplevel.proof (Proof.map_context (define_invariant_command logic name content))))
end

end

signature HOARE_LOGIC =
sig
type program
type range
val logic: Forward_Hoare.logic
val ex_program : program -> Forward_Hoare.ex_program
val program_ex : Forward_Hoare.ex_program -> program
val ex_range : range -> Forward_Hoare.ex_range
val range_ex : Forward_Hoare.ex_range -> range
end


functor Hoare_Logic(Logic: HOARE_LOGIC_ARGS): HOARE_LOGIC =
struct

open Forward_Hoare

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
fun join_hoare ctxt prog a r1 b r2 c h1 h2 = Logic.join_hoare ctxt (program_ex prog) a (range_ex r1) b (range_ex r2) c h1 h2
  |> apfst ex_range

val logic : logic = {
  serial = serial(),
  binding = Logic.binding,
  read_program = read_program,
  read_range = read_range,
  extract_range = extract_range,
  valid_range = valid_range,
  hoare_thm = Logic.hoare_thm,
  read_invariant = Logic.read_invariant,
  join_hoare = join_hoare
}

val _ = Context.>> (Context.map_theory (Logic_Data.map (Symtab.update_new (Binding.name_of Logic.binding, logic))))
end

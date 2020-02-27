signature HOARE_LOGIC_ARGS =
sig
type program
type range
val binding: binding
val read_program: Proof.context -> string -> program
val read_range: range option -> range context_parser
val pretty_range: Proof.context -> range -> Pretty.T
val read_invariant: Proof.context -> string -> term
val postcondition_generators: (term->term->term*(Proof.context->tactic)) context_parser Symtab.table
val join_hoare: Proof.context -> program -> term -> range -> term -> range -> term -> thm -> thm -> (range*thm)
val valid_range: program -> range -> bool
(* Contract: valid range *)
val extract_range: program -> range -> term
val hoare_thm: Proof.context -> term -> term -> term -> term (* pre prog post *)
val invariant_implication: Proof.context -> term -> term -> term
val program_morphism: morphism -> program -> program
end

structure Forward_Hoare =
struct

type 'a toolkit = {
  define: binding -> binding -> term -> 'a -> (term*thm*'a),
  declaration: declaration -> 'a -> 'a,
  context: 'a -> Context.generic,
  theorem: (thm -> 'a -> 'a) -> term -> 'a -> Proof.state,
  note: binding -> thm -> 'a -> 'a
}

val lthy_toolkit : local_theory toolkit = let

  fun define bind thm_bind prop lthy =
    case Local_Theory.define ((bind,NoSyn),((thm_bind,[]),prop)) lthy of
      ((const,(_,thm)),lthy) => (const,thm,lthy)
  val declaration = Local_Theory.declaration {syntax=false, pervasive=false}
  val context = Context.Proof
  fun theorem after_qed prop lthy = let
    fun after_qed' [[thm]] lthy = after_qed thm lthy
      | after_qed' _ _ = raise Match
    in Proof.theorem NONE after_qed' [[(prop, [])]] lthy end
  fun note bind thm lthy = Local_Theory.note ((bind,[]),[thm]) lthy |> snd
  in { define=define, declaration=declaration, context=context, theorem=theorem, note=note } end

val proof_toolkit : Proof.state toolkit = let

  fun define bind thm_bind prop state = 
    case Proof.map_context_result (Local_Defs.define [((bind,NoSyn),((thm_bind,[]),prop))]) state
      of ([(const,(_,thm))],state) => (const,thm,state)
       | _ => raise Match

  fun declaration decl = decl Morphism.identity |> Context.proof_map |> Proof.map_context
  val context = Proof.context_of #> Context.Proof
  fun theorem after_qed prop state = let
    fun after_qed' (_,[[thm]]) state = after_qed thm state
      | after_qed' _ _ = raise Match
    in Proof.have false NONE after_qed' [] [] 
       [((Binding.empty,[]),[(prop,[])])] true state |> snd end

  fun note bind thm state = 
    Proof.map_context_result (Proof_Context.note_thmss "" [((bind,[]),[([thm],[])])]) state |> snd

  in { define=define, declaration=declaration, context=context, theorem=theorem, note=note } end

fun the' _ (SOME x) = x
  | the' msg NONE = error (msg ())

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
  read_range: ex_range option -> ex_range context_parser,
  pretty_range: Proof.context -> ex_range -> Pretty.T,
  read_invariant: Proof.context -> string -> term,
  valid_range: ex_program -> ex_range -> bool,
  extract_range: ex_program -> ex_range -> term, (* TODO do we need that? *)
  hoare_thm: Proof.context -> term -> term -> term -> term,
  (* join_hoare ctxt prog a r1 b r2 c h1 h2
     returns thm {a}r1;r2{c} *)
  join_hoare: Proof.context -> ex_program -> term -> ex_range -> term -> ex_range -> term -> thm -> thm -> (ex_range*thm),
  postcondition_generators: (term->term->term*(Proof.context->tactic)) context_parser Symtab.table,
  invariant_implication: Proof.context -> term -> term -> term,
  program_morphism: morphism -> ex_program -> ex_program
}

structure Logic_Data = Theory_Data(
  type T = logic Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (fn (x,y) => #serial x = #serial y)
  val extend = I
)



fun get_logic thy name = Symtab.lookup (Logic_Data.get thy) name
fun get_the_logic thy name = get_logic thy name |> the' (fn () => "Unknown hoare logic " ^ name)
fun get_logic' ctxt = get_logic (Proof_Context.theory_of ctxt)

fun logic_name {binding, ...} = Binding.name_of binding

fun get_the_postcondition_generator logic make_post =
 Symtab.lookup (#postcondition_generators logic) make_post 
 |> the' (fn _ => "Unknown postcondition generator " ^ make_post ^ " in logic " ^ logic_name logic)

(* TODO remove *)
fun def' binding t lthy =
  let val thm_binding = Binding.suffix_name "_def" binding
      val ((const,(_,thm)),lthy) = Local_Theory.define ((binding,NoSyn),((thm_binding,[]),t)) lthy
      val _ = tracing ("Defining " ^ string_of_binding_const binding ^ " := " ^ Syntax.string_of_term lthy t)
  in ((const,thm),lthy) end
(* TODO remove *)
fun def'' binding t = Proof.map_context_result (def' binding t)

type var = string
type program = { serial: serial, binding: binding, code: ex_program, logic: string }

fun program_morphism thy m ({serial,binding,code,logic}:program) : program = let
  val logic' = get_logic thy logic |> the
  in {serial=serial, binding=binding, logic=logic,
      code = #program_morphism logic' m code} end

fun program_eq (p1,p2) = #serial p1 = #serial p2

type invariant = {
  serial: serial,
  logic: string,
  binding: binding,
  term: term,
  const: term,
  def_thm: thm
}

fun invariant_eq (i1,i2) = #serial i1 = #serial i2

type hoare = {
  serial: serial,
  binding: binding,
  range: ex_range,
  program: string,
  program_fragment_const: term,
  precondition: string,
  postcondition: string,
  valid: thm
}

fun hoare_morphism m ({serial,binding,range,program,program_fragment_const,precondition,postcondition,valid}:hoare): hoare = 
  {serial=serial, binding=binding, range=range, program=program, 
   program_fragment_const = Morphism.term m program_fragment_const,
   precondition=precondition, postcondition=postcondition,
   valid = Morphism.thm m valid}

fun hoare_eq (h1,h2) = #serial h1 = #serial h2

structure Hoare_Data = Generic_Data (
  type T = { invariants: invariant Symtab.table,
             hoares: hoare Symtab.table,
             programs: program Symtab.table,
             current_program: string option
  }
  val empty = { invariants=Symtab.empty, hoares=Symtab.empty,
    programs=Symtab.empty, current_program=NONE }
  fun merge (d1,d2) =
    { invariants = Symtab.merge invariant_eq (#invariants d1, #invariants d2),
      hoares = Symtab.merge hoare_eq (#hoares d1, #hoares d2),
      programs = Symtab.merge program_eq (#programs d1, #programs d2),
      current_program = NONE }
  fun extend {invariants,hoares,programs,current_program=_} =
    {invariants=invariants, hoares=hoares, programs=programs, current_program=NONE}
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
fun add_hoare0decl i m = add_hoare0 (hoare_morphism m i)
fun add_program0 p context = let
  val name = Binding.name_of (#binding p)
  val ctxt = map_programs (Symtab.update_new (name, p)) context
  val ctxt = set_current_program name ctxt
  in ctxt end
fun add_program0decl thy p m = add_program0 (program_morphism thy m p)
fun get_invariant ctxt name = Symtab.lookup (Hoare_Data.get ctxt |> #invariants) name
fun get_hoare ctxt name = Symtab.lookup (Hoare_Data.get ctxt |> #hoares) name
fun get_program ctxt name = Symtab.lookup (Hoare_Data.get ctxt |> #programs) name
fun get_the_program ctxt name = get_program ctxt name |> the' (fn _ => "Unknown program " ^ name)
fun get_current_program ctxt = Hoare_Data.get ctxt |> #current_program

fun invariant_morph m ({serial,logic,binding,term,const,def_thm}:invariant) : invariant =
 {serial=serial, logic=logic, binding=binding, term=Morphism.term m term,
   const=Morphism.term m const, def_thm=Morphism.thm m def_thm}

fun add_invariant (toolkit:'st toolkit) logic binding (invariant:term) st : invariant * 'st = let
  fun bind suffix = Binding.suffix_name suffix binding
  val (invariant_const,thm,st) = 
      #define toolkit (bind "_inv") (bind "_inv_def") invariant st
      (* def' (bind "_inv") invariant ctxt *)
  val info : invariant = {serial=serial(), logic=logic, binding=binding, const=invariant_const, term=invariant, def_thm=thm}
  val st = #declaration toolkit (fn m => add_invariant0 (invariant_morph m info)) st
  in (info,st) end

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

(* TODO remove *)
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

(* TODO remove *)
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

fun new_hoare (toolkit:'a toolkit) binding after_qed0 (program:string) range (precondition:string) (postcondition:string) (st:'a) : Proof.state = let
  val context = #context toolkit st
  val ctxt = Context.proof_of context
  (* val (ctxt,thy) = let  in (Context.proof_of context, Context.theory_of context) end *)
(*   val program = case program of 
    SOME program => program
  | NONE => get_current_program ctxt |> the *)
  val program = get_the_program context program
  val precondition = case get_invariant context precondition of
    SOME inv => inv | NONE => error ("Undefined precondition " ^ precondition)
  val postcondition = case get_invariant context postcondition of
    SOME inv => inv | NONE => error ("Undefined postcondition " ^ postcondition)
  (* val (postcondition,state) = Proof.map_context_result (add_invariant binding postcondition) state *)
  (* val (_,state) = add_hoare2 binding after_qed0 program range precondition postcondition state *)
  fun bind suffix = Binding.suffix_name suffix binding
  val logic = get_the_logic (Context.theory_of context) (#logic program)
  val _ = if #valid_range logic (#code program) range then ()
          else error ("Invalid range " ^ Pretty.string_of (#pretty_range logic ctxt range))
  val program_fragment = (#extract_range logic) (#code program) range
  val _ = tracing ("Range: " ^ (Pretty.string_of (#pretty_range logic ctxt range)))
  val _ = tracing ("Program fragment: " ^ Syntax.string_of_term ctxt program_fragment)
  val (program_fragment_const,_,st) = 
      #define toolkit (bind "_prog") (bind "_prog_def") program_fragment st
  val valid_prop = #hoare_thm logic ctxt (#const precondition) program_fragment (#const postcondition)
  fun after_qed valid st = let
      val info : hoare = {serial=serial(), binding=binding, range=range,
        precondition=Binding.name_of (#binding precondition),
        postcondition=Binding.name_of (#binding postcondition),
        program_fragment_const=program_fragment_const,
        program=program |> #binding |> Binding.name_of,
        valid=valid}
      val st = #note toolkit (Binding.suffix_name "_valid" binding) valid st
      val st = #declaration toolkit (add_hoare0decl info) st
      in after_qed0 (st, info) end
  val state = #theorem toolkit after_qed valid_prop st

in state end


fun parse_src expect ctxt (parser:'a context_parser) (src:Token.src) : 'a = let
  val eof = Parse.group expect Parse.eof |> Scan.lift
  val (result,_) = Scan.catch (parser --| eof) (Context.Proof ctxt, src @ [Token.eof])
  (* val _ = if null rest then () else error "rest" *)
  in result end

fun new_hoare_auto (toolkit:'a toolkit) binding after_qed0 (program:string) range (precondition:string) 
    (postcondition:binding) (make_post:string) (make_post_args:Token.src) (st:'a) : Proof.state = let
  val context = #context toolkit st
  val ctxt = Context.proof_of context
  val program' = get_program context program |> the
  val logic = get_logic (Context.theory_of context) (#logic program') |> the
  val program_fragment = (#extract_range logic) (#code program') range
  val precondition' = case get_invariant context precondition of
    SOME inv => inv | NONE => error ("Undefined precondition " ^ precondition)
  val make_post' = get_the_postcondition_generator logic make_post
  val make_post' = parse_src (fn _ =>  "end of arguments to " ^ make_post) ctxt make_post' make_post_args
  val (post,tac) = make_post' program_fragment (#const precondition')
  val (post,st) = add_invariant toolkit (#logic program') postcondition post st
(* Proof.map_context_result (add_invariant logic postcondition post) state *)
  val state = new_hoare toolkit binding after_qed0 program range precondition (Binding.name_of postcondition) st
  val (state,_) = Proof.apply (Method.Basic (Method.unfold [#def_thm post]), Position.no_range) state
    |> Seq.first_result "could not unfold definition of postcondition (internal error)"
  val (state,_) = Proof.apply (Method.Basic (fn ctxt => SIMPLE_METHOD (tac ctxt)), Position.no_range) state
    |> Seq.first_result "could not solve proof obligation"

  in state end

fun join_hoare (toolkit:'a toolkit) binding (hoare1:string) (hoare2:string) (st:'a) = let
  val context = #context toolkit st
  val ctxt = Context.proof_of context
  val hoare1' = get_hoare context hoare1 |> the
  val hoare2' = get_hoare context hoare2 |> the
  val program = #program hoare1'
  val _ = if #program hoare1' <> #program hoare2' then error "mismatch" else ()
  val _ = if #postcondition hoare1' <> #precondition hoare2' then error "mismatch" else ()
  val program' = program |> get_program context |> the
  val logic = program' |> #logic |> get_logic' ctxt |> the
  val a = hoare1' |> #precondition |> get_invariant context |> the |> #const
  val b = hoare1' |> #postcondition |> get_invariant context |> the |> #const
  val c = hoare2' |> #postcondition |> get_invariant context |> the |> #const
  val (range,joined_thm) = #join_hoare logic ctxt (#code program') a (#range hoare1') b (#range hoare2') c
          (#valid hoare1') (#valid hoare2')
  val program_fragment = (#extract_range logic) (#code program') range
  val (program_fragment_const,_,st) = 
      #define toolkit (Binding.suffix_name "_prog" binding) (Binding.suffix_name "_prog_def" binding) program_fragment st

  val st = #note toolkit (Binding.suffix_name "_valid" binding) joined_thm st

  val info : hoare = {serial=serial(), binding=binding, range=range,
    precondition= #precondition hoare1',
    postcondition= #postcondition hoare2',
    program_fragment_const=program_fragment_const,
    program=program,
    valid=joined_thm
  }
  
  val st = #declaration toolkit (add_hoare0decl info) st

  in (st,info) end

(* (* Unused? *)
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
in state end *)

fun extend_hoare_auto (toolkit:'a toolkit) binding (previous:string) after_qed0 range (postcondition:binding)
    (make_post:string) (make_post_args:Token.src) (st:'a) = let
  val context = #context toolkit st
  (* val ctxt = Context.proof_of context *)
  val binding_step = Binding.suffix_name "_step" binding
  val previous_hoare = get_hoare context previous |> the
  val program = #program previous_hoare
  val precondition = #postcondition previous_hoare
  fun after_qed (st, hoare) = let
    val (st, joined_hoare) = join_hoare toolkit binding previous (Binding.name_of binding_step) st
    in after_qed0 (st, hoare, joined_hoare) end
  val state = new_hoare_auto toolkit binding_step after_qed program range precondition postcondition make_post make_post_args st
in state end

fun define_program_command (toolkit:'a toolkit) logic binding content (st:'a) : 'a = let
  val context = #context toolkit st
  val ctxt = Context.proof_of context
  val thy = Context.theory_of context
  val logic' = get_logic thy logic |> the
  val program = #read_program logic' ctxt content
  val st = #declaration toolkit (add_program0decl thy 
      {serial=serial(), binding=binding, logic=logic, code=program}) st
in st end

val _ = let
  val logic_parser = Parse.$$$ "(" |-- Parse.name --| Parse.$$$ ")"
  val name_parser = Parse.binding --| Parse.$$$ ":"
  val content_parser = Parse.embedded
  val parser = logic_parser -- name_parser -- content_parser
in
  Outer_Syntax.command \<^command_keyword>\<open>program\<close> "Declare a program"
    (parser >> (fn ((logic,name),content) => Toplevel.proof
      (define_program_command proof_toolkit logic name content)))
end

fun define_invariant_command (toolkit:'a toolkit) logic name content (st:'a) : 'a = let 
  val context = #context toolkit st
  val logic' = get_logic (Context.theory_of context) logic |> the
  val term = #read_invariant logic' (Context.proof_of context) content
  val _ = tracing ("Declaring invariant "^ string_of_binding_invariant name ^ " in logic " ^ string_of_binding_logic (#binding logic'))
  val (_,st) = add_invariant toolkit logic name term st
in st end

val _ = let
  val logic_parser = Parse.$$$ "(" |-- Parse.name --| Parse.$$$ ")"
  val name_parser = Parse.binding --| Parse.$$$ ":"
  val content_parser = Parse.group (fn _ => "invariant") (Parse.inner_syntax Parse.embedded)
  val parser = logic_parser -- name_parser -- content_parser
in
  Outer_Syntax.command \<^command_keyword>\<open>invariant\<close> "Declare an invariant"
    (parser >> (fn ((logic,name),content) => Toplevel.proof 
        (define_invariant_command proof_toolkit logic name content)))
end


fun tokens_parser stop : Token.src parser = Scan.many (fn tok => not (stop tok orelse Token.is_eof tok orelse Token.is_error tok))

fun hoare_command (toolkit:'a toolkit) (name:binding) (extends:string option) (range:Token.src) (pre:string option) (post:binding)
   (make_post:string) (make_post_args:Token.src) (st:'a) : Proof.state = let
  val context = #context toolkit st
  val ctxt = Context.proof_of context
  (* val thy = Proof.theory_of state *)
  val program = get_current_program context |> the
  val program' = get_program context program |> the
  val logic = get_logic (Context.theory_of context) (#logic program') |> the
  val range' = parse_src (K "end of range description") ctxt (#read_range logic NONE) range
  val state = case extends of
    NONE => (case pre of
             NONE => error "Please specify precondition (pre) or previous Hoare judgment (extends)"
             | SOME pre => new_hoare_auto toolkit name fst program range' pre post make_post make_post_args st)
    | SOME previous => extend_hoare_auto toolkit name previous #1 range' post make_post make_post_args st
  in state end

val _ = let
  val name_parser = Parse.binding --| Parse.$$$ ":"
  (* TODO: parse program name *)
  val extends_parser = Args.$$$ "extends" |-- Parse.name |> Scan.option
  val range_parser = Args.$$$ "range" |-- tokens_parser
    (Token.keyword_with (fn x => x="pre" orelse x="post"))
  val pre_parser = Args.$$$ "pre" |-- Parse.name |> Scan.option
  val make_post_parser = Parse.name -- tokens_parser (K false)
  val post_parser = Args.$$$ "post" |-- Parse.binding --| Args.$$$ "=" -- make_post_parser
  val parser = name_parser -- extends_parser -- range_parser -- pre_parser -- post_parser
in
  Outer_Syntax.command \<^command_keyword>\<open>hoare\<close> "State a Hoare triple"
    (parser >> (fn ((((name,extends),range),pre),(post,(make_post,make_post_args))) => 
      Toplevel.proof (hoare_command proof_toolkit name extends range pre post make_post make_post_args)))
end

fun invariant_has_command (toolkit:'a toolkit) (binding:binding) (invariant:string) (term:string) (st:'a) : Proof.state = let
  val context = #context toolkit st
  val ctxt = Context.proof_of context
  val invariant = get_invariant context invariant |> the' (fn _ => "Unknown invariant " ^ invariant)
  val logic = get_logic (Context.theory_of context) (#logic invariant) |> the
  val term = #read_invariant logic ctxt term
  (* val _ = \<^print> (invariant,term) *)
  val goal = #invariant_implication logic ctxt (#const invariant) term
  fun after_qed thm = #note toolkit binding thm
  val state = #theorem toolkit after_qed goal st
in state end

val _ = let
  val binding_parser = Parse.binding --| Args.$$$ ":"
  val invariant_parser = Parse.name --| (Args.$$$ "\<rightarrow>" || Args.$$$ "->")
  val parser = binding_parser -- invariant_parser -- Parse.term
in
  Outer_Syntax.command \<^command_keyword>\<open>invariant_has\<close> "Derive a fact about an invariant"
    (parser >> (fn ((binding,invariant),term) => Toplevel.proof (invariant_has_command proof_toolkit binding invariant term)))
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

fun ex_range range = Ex_Range (Range range)
fun range_ex (Ex_Range (Range prog)) = prog
  | range_ex (Ex_Range e) = err ("range_ex: " ^ \<^make_string> e)

fun read_range relative = 
  Logic.read_range (Option.map range_ex relative) >> ex_range

fun pretty_range ctxt range = Logic.pretty_range ctxt (range_ex range)

fun valid_range prog range = Logic.valid_range (program_ex prog) (range_ex range)
fun extract_range prog range = Logic.extract_range (program_ex prog) (range_ex range)
fun join_hoare ctxt prog a r1 b r2 c h1 h2 = Logic.join_hoare ctxt (program_ex prog) a (range_ex r1) b (range_ex r2) c h1 h2
  |> apfst ex_range

fun program_morphism m prog = ex_program (Logic.program_morphism m (program_ex prog))

val logic : logic = {
  serial = serial(),
  binding = Logic.binding,
  read_program = read_program,
  read_range = read_range,
  pretty_range = pretty_range,
  extract_range = extract_range,
  valid_range = valid_range,
  hoare_thm = Logic.hoare_thm,
  read_invariant = Logic.read_invariant,
  join_hoare = join_hoare,
  postcondition_generators = Logic.postcondition_generators,
  invariant_implication = Logic.invariant_implication,
  program_morphism = program_morphism
}

val _ = Context.>> (Context.map_theory (Logic_Data.map (Symtab.update_new (Binding.name_of Logic.binding, logic))))
end

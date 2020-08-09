structure Forward_Hoare =
struct

type 'a toolkit = {
  define: binding -> binding -> term -> 'a -> (term*thm*'a),
  declaration: declaration -> 'a -> 'a,
  context: 'a -> Context.generic,
  theorem: (thm -> 'a -> 'a) -> term -> 'a -> Proof.state,
  note: binding -> thm -> 'a -> 'a,
  qed: Proof.state -> 'a
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
  val qed = Proof.global_done_proof
  in { define=define, declaration=declaration, context=context, theorem=theorem, note=note, qed=qed } end

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

  val qed = Proof.local_done_proof

  in { define=define, declaration=declaration, context=context, theorem=theorem, note=note, qed=qed } end

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


(* datatype ex_program = Ex_Program of exn *)
datatype ex_range = Ex_Range of exn
datatype ex_options = Ex_Options of exn

type logic = {
  binding: binding,
  serial: serial,
  program_term_typ: ex_options -> typ,
  check_program: Proof.context -> term -> unit,
  read_range: ex_options -> ex_range option -> ex_range context_parser,
  pretty_range: Proof.context -> ex_range -> Pretty.T,
  invariant_typ: ex_options -> typ,
  check_invariant: Proof.context -> term -> unit,
  (* read_invariant: Proof.context -> string -> term, *)
  (* valid_range: term -> ex_range -> bool, *)
  extract_range: Proof.context -> ex_range -> term,
  hoare_thm: Proof.context -> term -> term -> term -> term,
  join_hoare: Proof.context -> term -> ex_range -> term -> ex_range -> term -> thm -> thm -> (ex_range*thm),
  postcondition_generators: (term->term->term*(Proof.context->tactic)) context_parser Symtab.table,
  invariant_implication: Proof.context -> term -> term -> term,
  invariant_implication_lhs: term -> term,
  invariant_implication_syntax: Proof.context -> term -> term -> term,
  invariant_parse_translation: Proof.context -> term -> term -> term,
  (* program_morphism: morphism -> term -> term *)
  default_options: ex_options,
  set_option: string -> string -> Proof.context -> morphism -> ex_options -> ex_options
}

fun name_of_logic ({binding,...}:logic) = Binding.name_of binding
fun same_logic (l1:logic) (l2:logic) = (#serial l1 = #serial l2)

structure Logic_Data = Theory_Data(
  type T = logic Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (fn (x,y) => same_logic x y)
  val extend = I
)



fun get_logic thy name = Symtab.lookup (Logic_Data.get thy) name
fun get_logics thy = Logic_Data.get thy
fun get_the_logic thy name = get_logic thy name |> the' (fn () => "Unknown hoare logic " ^ name)
fun get_logic' ctxt = get_logic (Proof_Context.theory_of ctxt)
fun get_the_logic' ctxt = get_the_logic (Proof_Context.theory_of ctxt)

fun get_the_postcondition_generator logic make_post =
 Symtab.lookup (#postcondition_generators logic) make_post 
 |> the' (fn _ => "Unknown postcondition generator " ^ make_post ^ " in logic " ^ name_of_logic logic)

type var = string
type program = { serial: serial, binding: binding, code: term, logic: string }

fun program_morphism m ({serial,binding,code,logic}:program) : program = let
  in {serial=serial, binding=binding, logic=logic,
      code = Morphism.term m code} end

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
  logic: logic,
  binding: binding,
  range: ex_range,
  (* program: string, *)
  program_fragment_const: term,
  precondition: string,
  postcondition: string,
  valid: thm
}

fun hoare_morphism m ({serial,logic,binding,range,program_fragment_const,precondition,postcondition,valid}:hoare): hoare = 
  {serial=serial, logic=logic, binding=binding, range=range, 
   program_fragment_const = Morphism.term m program_fragment_const,
   precondition=precondition, postcondition=postcondition,
   valid = Morphism.thm m valid}

fun hoare_eq (h1,h2) = #serial h1 = #serial h2

structure Hoare_Data = Generic_Data (
  type T = { invariants: invariant Symtab.table,
             hoares: hoare Symtab.table,
             programs: program Symtab.table,
             current_logic: logic option,
             options: ex_options Symtab.table
  }
  val empty = { invariants=Symtab.empty, hoares=Symtab.empty,
    programs=Symtab.empty, current_logic=NONE, options=Symtab.empty }
  fun merge (d1,d2) =
    { invariants = Symtab.merge invariant_eq (#invariants d1, #invariants d2),
      hoares = Symtab.merge hoare_eq (#hoares d1, #hoares d2),
      programs = Symtab.merge program_eq (#programs d1, #programs d2),
      current_logic = NONE, options = Symtab.empty }
  fun extend {invariants,hoares,programs,current_logic=_,options} =
    {invariants=invariants, hoares=hoares, programs=programs, current_logic=NONE, options=options}
)

fun map_invariants f = Hoare_Data.map (fn {invariants,hoares,programs,current_logic,options} => 
  {invariants=f invariants, hoares=hoares, programs=programs, current_logic=current_logic, options=options})
fun map_hoares f = Hoare_Data.map (fn {invariants,hoares,programs,current_logic,options} => 
  {invariants=invariants, hoares=f hoares, programs=programs, current_logic=current_logic, options=options})
fun map_programs f = Hoare_Data.map (fn {invariants,hoares,programs,current_logic,options} => 
  {invariants=invariants, hoares=hoares, programs=f programs, current_logic=current_logic, options=options})
fun map_options f = Hoare_Data.map (fn {invariants,hoares,programs,current_logic,options} => 
  {invariants=invariants, hoares=hoares, programs=programs, current_logic=current_logic, options=f options})
fun set_current_logic (logic:logic) = Hoare_Data.map (fn {invariants,hoares,programs,current_logic=_,options} => 
  {invariants=invariants, hoares=hoares, programs=programs, current_logic=SOME logic, options=options})
fun add_invariant0 i = map_invariants (Symtab.update_new (Binding.name_of (#binding i), i))
fun add_hoare0 i = map_hoares (Symtab.update_new (Binding.name_of (#binding i), i))
fun add_hoare0decl i m = add_hoare0 (hoare_morphism m i)
fun get_invariant context name = Symtab.lookup (Hoare_Data.get context |> #invariants) name
fun get_invariants context = Hoare_Data.get context |> #invariants
fun get_the_invariant context name = get_invariant context name |> the' (fn _ => "Unknown invariant " ^ name)
fun get_hoare context name = Symtab.lookup (Hoare_Data.get context |> #hoares) name
fun get_the_hoare context name = get_hoare context name |> the' (fn _ => "Unknown Hoare judgment " ^ name)
(* TODO check whether 'name' contains markup, if so, raise error. Same in all other getters *)
fun get_program context name = Symtab.lookup (Hoare_Data.get context |> #programs) name
fun get_the_program context name = get_program context name |> the' (fn _ => "Unknown program " ^ name)
fun get_current_logic context = Hoare_Data.get context |> #current_logic
fun get_the_current_logic context = get_current_logic context |> the' (fn _ => "No current logic")

structure Hoare_Proof_Data = Proof_Data (
  (* current_invariant is local to a proof obligation created by a hoare' command *)
  type T = { current_invariant: invariant option }
  fun init _ = { current_invariant=NONE }
)


fun get_options logic context = 
  case Symtab.lookup (Hoare_Data.get context |> #options) (name_of_logic logic) of 
    SOME options => options
  | NONE => #default_options logic

fun set_option (logic:logic) name content m context = let
  val ctxt = Context.proof_of context
  val options = get_options logic context
  val options = #set_option logic name content ctxt m options
  val context = map_options (Symtab.update (name_of_logic logic, options)) context
  in context end



fun set_current_invariant invariant = Hoare_Proof_Data.map (fn
  { current_invariant=_ } => { current_invariant = SOME invariant })
fun get_current_invariant ctxt = Hoare_Proof_Data.get ctxt |> #current_invariant
val get_the_current_invariant = get_current_invariant
  #> the' (fn _ => "No current invariant")
val get_current_invariant_def = get_current_invariant #> Option.map #def_thm
val get_the_current_invariant_def = get_current_invariant_def
  #> the' (fn _ => "No current invariant")

fun invariant_morph m ({serial,logic,binding,term,const,def_thm}:invariant) : invariant =
 {serial=serial, logic=logic, binding=binding, term=Morphism.term m term,
   const=Morphism.term m const, def_thm=Morphism.thm m def_thm}

fun catch_internal_error logic func f x = f x
   handle TYPE(msg, Ts, ts) => let 
     val name = logic |> string_of_binding_logic
   in raise TYPE("Internal error " ^ func ^ " (logic " ^ name ^ "): " ^ msg, Ts, ts) end

fun add_invariant (toolkit:'st toolkit) (logic:logic) binding (invariant:term) st : invariant * 'st = let
  fun bind suffix = Binding.suffix_name suffix binding
  val (invariant_const,thm,st) = 
      #define toolkit (bind "_inv") (bind "_inv_def") invariant st
      (* def' (bind "_inv") invariant ctxt *)
  val info : invariant = {serial=serial(), logic = name_of_logic logic, binding=binding, const=invariant_const, term=invariant, def_thm=thm}
  val st = #declaration toolkit (fn m => add_invariant0 (invariant_morph m info)) st
  in (info,st) end

fun new_hoare (toolkit:'a toolkit) binding after_qed0 (logic:logic) range (precondition:string) (postcondition:string) (st:'a) : Proof.state = let
  val context = #context toolkit st
  val ctxt = Context.proof_of context
  (* val program = get_the_program context program *)
  val precondition = case get_invariant context precondition of
    SOME inv => inv | NONE => error ("Undefined precondition " ^ precondition)
  val postcondition = case get_invariant context postcondition of
    SOME inv => inv | NONE => error ("Undefined postcondition " ^ postcondition)
  fun bind suffix = Binding.suffix_name suffix binding
  (* val logic = get_the_logic (Context.theory_of context) (#logic program) *)
(*   val _ = if #valid_range logic range then ()
          else error ("Invalid range " ^ Pretty.string_of (#pretty_range logic ctxt range)) *)
  val program_fragment = (#extract_range logic) ctxt range
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
        logic = logic,
        (* program=program |> #binding |> Binding.name_of, *)
        valid=valid}
      val st = #note toolkit (Binding.suffix_name "_valid" binding) valid st
      val st = #declaration toolkit (add_hoare0decl info) st
      in after_qed0 (st, info) end
  val state = #theorem toolkit after_qed valid_prop st

in state end


fun parse_src expect ctxt (parser:'a context_parser) (src:Token.src) : 'a = let
  val eof = Parse.group expect Parse.eof |> Scan.lift
  val (result,_) = Scan.catch (parser --| eof) (Context.Proof ctxt, src @ [Token.eof])
  in result end

fun new_hoare_auto (toolkit:'a toolkit) binding after_qed0 (logic:logic) range (precondition:string) 
    (postcondition:binding) (make_post:string) (make_post_args:Token.src) (st:'a) : Proof.state = let
  val context = #context toolkit st
  val ctxt = Context.proof_of context
  val program_fragment = (#extract_range logic) ctxt range
  val precondition' = case get_invariant context precondition of
    SOME inv => inv | NONE => error ("Undefined precondition " ^ precondition)
  val make_post' = get_the_postcondition_generator logic make_post
  val make_post' = parse_src (fn _ =>  "end of arguments to " ^ make_post) ctxt make_post' make_post_args
  val (post,tac) = make_post' program_fragment (#const precondition')
  val _ = catch_internal_error (#binding logic) ("typechecking result of postcondition generator "^make_post)
            (Sign.cert_term (Proof_Context.theory_of ctxt)) post
  val (post,st) = add_invariant toolkit logic postcondition post st
  val state = new_hoare toolkit binding after_qed0 logic range precondition (Binding.name_of postcondition) st
  val (state,_) = Proof.apply (Method.Basic (Method.unfold [#def_thm post]), Position.no_range) state
    |> Seq.first_result "could not unfold definition of postcondition (internal error)"
  val (state,_) = Proof.apply (Method.Basic (fn ctxt => SIMPLE_METHOD (tac ctxt)), Position.no_range) state
    |> Seq.first_result "could not solve proof obligation"

  in state end

fun join_hoare (toolkit:'a toolkit) binding (hoare1:string) (hoare2:string) (st:'a) = let
  val context = #context toolkit st
  val ctxt = Context.proof_of context
  val hoare1' = get_the_hoare context hoare1
  val hoare2' = get_the_hoare context hoare2
  (* val program = #program hoare1' *)
  (* val _ = if #program hoare1' <> #program hoare2' then error "mismatch" else () *)
  val _ = if same_logic (#logic hoare1') (#logic hoare2') then () else error "mismatch"
  val _ = if #postcondition hoare1' <> #precondition hoare2' then error "mismatch" else ()
  (* val program' = program |> get_the_program context *)
  (* val logic = program' |> #logic |> get_the_logic' ctxt *)
  val a = hoare1' |> #precondition |> get_the_invariant context |> #const
  val b = hoare1' |> #postcondition |> get_the_invariant context |> #const
  val c = hoare2' |> #postcondition |> get_the_invariant context |> #const
  val logic = #logic hoare1'
  val (range,joined_thm) = #join_hoare logic ctxt a (#range hoare1') b (#range hoare2') c
          (#valid hoare1') (#valid hoare2')
  val program_fragment = (#extract_range logic) ctxt range
  val (program_fragment_const,_,st) = 
      #define toolkit (Binding.suffix_name "_prog" binding) (Binding.suffix_name "_prog_def" binding) program_fragment st

  val st = #note toolkit (Binding.suffix_name "_valid" binding) joined_thm st

  val info : hoare = {serial=serial(), binding=binding, range=range,
    precondition= #precondition hoare1',
    postcondition= #postcondition hoare2',
    program_fragment_const=program_fragment_const,
    logic = logic,
    (* program=program, *)
    valid = joined_thm
  }
  
  val st = #declaration toolkit (add_hoare0decl info) st

  in (st,info) end

(* (* Unused? *)
fun extend_hoare binding (previous:string) after_qed0 range (postcondition:string) state = let
  val ctxt = Proof.context_of state
  val binding_step = Binding.suffix_name "_step" binding
  val previous_hoare = get_the_hoare ctxt previous
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
  val binding_step = Binding.suffix_name "_step" binding
  val previous_hoare = get_the_hoare context previous
  val logic = #logic previous_hoare
  val precondition = #postcondition previous_hoare
  fun after_qed (st, hoare) = let
    val (st, joined_hoare) = join_hoare toolkit binding previous (Binding.name_of binding_step) st
    in after_qed0 (st, hoare, joined_hoare) end
  val state = new_hoare_auto toolkit binding_step after_qed logic range precondition postcondition make_post make_post_args st
in state end


fun read_term_typed ctxt T str = let
  val raw_term = Syntax.parse_term ctxt str
  val typed = Const("_type_constraint_", T --> T) $ raw_term
  val t = Syntax.check_term ctxt typed
  in t end

fun set_current_logic_command (toolkit:'a toolkit) (logic:logic) st = let
  val _ = tracing ("Setting current logic to " ^ name_of_logic logic)
  in #declaration toolkit (K (set_current_logic logic)) st end

fun define_program_command (toolkit:'a toolkit) (logic:string) binding content (st:'a) : 'a = let
  val context = #context toolkit st
  val ctxt = Context.proof_of context
  val thy = Context.theory_of context
  val logic' = get_the_logic thy logic
  val options = get_options logic' context
  val program = read_term_typed ctxt (#program_term_typ logic' options) content
  val _ = #check_program logic' ctxt program
  val st = set_current_logic_command toolkit logic' st
  val (_,_,st) = #define toolkit binding (Binding.suffix_name "_def" binding) program st
  val name = Binding.name_of binding
(* TODO: instead of argument p, use variable prog *)
  fun add_program0decl (p:program) (m:morphism) context = let
    val context = map_programs (Symtab.update_new (name, program_morphism m p)) context
    val context = set_option logic' "@last_program" name m context
    in context end
  val st = #declaration toolkit (add_program0decl
      {serial=serial(), binding=binding, logic=logic, code=program}) st
in st end

fun set_option_command (toolkit:'a toolkit) (logic:string) name content (st:'a) : 'a = let
  val context = #context toolkit st
  (* val ctxt = Context.proof_of context *)
  val thy = Context.theory_of context
  val logic' = get_the_logic thy logic
  val st = set_current_logic_command toolkit logic' st
  val st = #declaration toolkit (set_option logic' name content) st
in st end

fun define_invariant_command (toolkit:'a toolkit) logic name content (st:'a) : 'a = let 
  val context = #context toolkit st
  val ctxt = Context.proof_of context
  val logic' = get_the_logic (Context.theory_of context) logic
  val options = get_options logic' context
  val term = read_term_typed ctxt (#invariant_typ logic' options) content
  val _ = #check_invariant logic' ctxt term
  val _ = tracing ("Declaring invariant "^ string_of_binding_invariant name ^ " in logic " ^ string_of_binding_logic (#binding logic'))
  val st = set_current_logic_command toolkit logic' st
  val (_,st) = add_invariant toolkit logic' name term st
in st end

fun tokens_parser stop : Token.src parser = Scan.many (fn tok => not (stop tok orelse Token.is_eof tok orelse Token.is_error tok))

fun hoare_command (toolkit:'a toolkit) (name:binding) (extends:string option) (range:Token.src) (pre:string option) (post:binding)
   (make_post:string) (make_post_args:Token.src) (st:'a) : Proof.state = let
  val context = #context toolkit st
  val ctxt = Context.proof_of context
  val logic = get_the_current_logic context
  val options = get_options logic context
  val range' = parse_src (K "end of range description") ctxt (#read_range logic options NONE) range
  val st = set_current_logic_command toolkit logic st
  val state = case extends of
    NONE => (case pre of
             NONE => error "Please specify precondition (pre) or previous Hoare judgment (extends)"
             | SOME pre => new_hoare_auto toolkit name fst logic range' pre post make_post make_post_args st)
    | SOME previous => extend_hoare_auto toolkit name previous #1 range' post make_post make_post_args st
  in state end

fun invariant_has_command (toolkit:'a toolkit) (binding:binding) (invariant:string) (term:string) (st:'a) : Proof.state = let
  val context = #context toolkit st
  val ctxt = Context.proof_of context
  val invariant = get_invariant context invariant |> the' (fn _ => "Unknown invariant " ^ invariant)
  val logic = get_logic (Context.theory_of context) (#logic invariant) |> the' (fn _ => "Unknown logic " ^ #logic invariant)
  val options = get_options logic context
  val term = read_term_typed ctxt (#invariant_typ logic options) term
  val _ = #check_invariant logic ctxt term
  val goal = #invariant_implication logic ctxt (#const invariant) term |> HOLogic.mk_Trueprop
  fun after_qed thm = #note toolkit binding thm
  (* val st = set_current_logic_command toolkit logic st *)
  val state = #theorem toolkit after_qed goal st
  val state = Proof.map_context (set_current_invariant invariant) state
in state end

fun filter_OF (thms1:thm list) (thms2:thm list) : thm list = 
  thms1 |> map_filter (fn thm' => SOME (thm' OF thms2) handle THM _ => NONE)

(* fun filter_inst ctxt (thms:thm list) var value : thm list =
  thms |> map_filter (fn thm' => SOME (Drule.infer_instantiate ctxt [(var,value)] thm') handle THM _ => NONE) *)

(* Raises TERM or TYPE if not found *)
fun get_invariant_from_implication' (ctxt:Proof.context) (logic:logic) (t:term) = let
  val const = #invariant_implication_lhs logic t
  val inv = case get_invariants (Context.Proof ctxt) |> Symtab.get_first 
                   (fn (_,inv) => if #const inv = const then SOME inv else NONE)
            of SOME inv => inv | NONE => raise TERM("get_invariant_from_implication'", [t,const])
in inv end

fun get_invariant_from_implication (ctxt:Proof.context) (t:term) = let
  val inv = get_logics (Proof_Context.theory_of ctxt) |> Symtab.get_first
    (fn (_,logic) => SOME (get_invariant_from_implication' ctxt logic t)
        handle TERM _ => NONE | TYPE _ => NONE)
  in inv |> the' (fn _ => "Could not identify invariant in the lhs of " ^ Syntax.string_of_term ctxt t) end

fun current_invariant_tac thms ctxt = SUBGOAL (fn (t,i) => let
  val thms = thms ctxt
  val inv = case get_current_invariant ctxt of SOME inv => inv
              | NONE => let
                  val t = HOLogic.dest_Trueprop (Logic.strip_assums_concl t) handle TERM(msg,Ts) => raise TERM("current_invariant_tac: "^msg,Ts)
                  in get_invariant_from_implication ctxt t end
  (* val logic = #logic inv *)
  val inv_def = #def_thm inv
  val thms_inst = filter_OF thms [inv_def]  
  val inv_markup_name = #binding inv |> string_of_binding_invariant
  val _ = if null thms_inst 
          then error ("No rules found that match invariant " ^ inv_markup_name) else ()
  val _ = Pretty.fbreaks (Pretty.str ("Available rules for invariant " ^ inv_markup_name ^ ":") ::
              map (Pretty.item o single o Syntax.pretty_term ctxt o Thm.prop_of) thms_inst)
          |> Pretty.block |> Pretty.string_of |> tracing
  in
    resolve_tac ctxt thms_inst i
(*     THEN'
    solve_tac ctxt [inv_def] *)
  end)

val invariant_untouched_tac = current_invariant_tac (fn ctxt => Named_Theorems.get ctxt \<^named_theorems>\<open>hoare_untouched\<close>)
val invariant_updated_tac = current_invariant_tac (fn ctxt => Named_Theorems.get ctxt \<^named_theorems>\<open>hoare_updated\<close>)
val invariant_wp_tac = current_invariant_tac (fn ctxt => Named_Theorems.get ctxt \<^named_theorems>\<open>hoare_wp\<close>)

val _ = Theory.setup
  (Attrib.setup \<^binding>\<open>current_invariant_def\<close> 
  (Scan.succeed (Thm.rule_attribute [] (fn context => fn _ =>
    case Context.proof_of context |> get_current_invariant_def of
      NONE => Drule.dummy_thm
    | SOME thm => thm)))
    "[[current_invariant_def]] gives the definition of the currently investigated invariant)")

(* Adapted from syntax_phases.ML *)
fun mark_atoms tm =
  let
    fun mark ((t as Const (c, _)) $ u) =
          if member (op =) Pure_Thy.token_markers c
          then t $ u else mark t $ mark u
      | mark (t $ u) = mark t $ mark u
      | mark (Abs (x, T, t)) = Abs (x, T, mark t)
      | mark (Const (c, T)) =
          Const (Lexicon.mark_const c, T)
      | mark (Free (x, T)) =
          Const (Lexicon.mark_fixed x, T)
      | mark (t as Var (xi, T)) =
          if xi = Auto_Bind.dddot then Const ("_DDDOT", T)
          else Syntax.const "_var" $ t
      | mark a = a;
  in mark tm end;

fun invariant_implication_tr ctxt [inv1_var,inv2] = let
(* val _ = \<^print> inv1_var *)
    val inv1_name = case inv1_var of Free(n,_) => n | _ => error "_invariant_implication parse_translation 1"
    val inv1 = get_the_invariant (Context.Proof ctxt) inv1_name
    val logic = get_the_logic' ctxt (#logic inv1)
    val inv1_const = #const inv1 |> mark_atoms
    val inv2_tr = inv2 |> #invariant_parse_translation logic ctxt (#const inv1)
(* Tmp_Hoare.tr_EXPR2_like HOLogic.boolT ctxt inv2 (* TODO also EXPR_like & not hardcoded *) *)
(* val inv1_const = Free("step2_inv",fastype_of inv1_const) *)
    val impl = #invariant_implication_syntax logic ctxt inv1_const inv2_tr
(* val _ = impl |> \<^print> *)
(* val _ = impl_raw |> Syntax.string_of_term ctxt |> writeln *)
  in impl end
  | invariant_implication_tr _ ts = raise TERM("invariant_implication_tr", ts)

(** Isar command **)

val binding_parser = Parse.binding --| Args.$$$ ":"
val invariant_parser = Parse.name --| (Args.$$$ "\<rightarrow>" || Args.$$$ "->")
fun invariant_has_parser toolkit = binding_parser -- invariant_parser -- Parse.term
>> (fn ((binding,invariant),term) => invariant_has_command toolkit binding invariant term)

val logic_parser = Parse.$$$ "(" |-- Parse.name --| Parse.$$$ ")"
val name_parser = Parse.binding --| Parse.$$$ ":"
val content_parser = Parse.embedded
fun declare_program_parser toolkit = (logic_parser -- name_parser -- content_parser)
  >> (fn ((logic,name),content) => define_program_command toolkit logic name content)

val logic_parser = Parse.$$$ "(" |-- Parse.name --| Parse.$$$ ")"
val name_parser = Parse.binding --| Parse.$$$ ":"
val content_parser = Parse.group (fn _ => "invariant") (Parse.inner_syntax Parse.embedded)

fun declare_invariant_parser toolkit = logic_parser -- name_parser -- content_parser
 >> (fn ((logic,name),content) => define_invariant_command toolkit logic name content)

fun config_parser toolkit = (logic_parser -- Parse.name --| Parse.$$$ "=" -- content_parser)
  >> (fn ((logic,name),content) => set_option_command toolkit logic name content)



(* val _ = Outer_Syntax.command \<^command_keyword>\<open>invariant\<close> "Declare an invariant"
    (declare_invariant_parser >> (fn ((logic,name),content) => Toplevel.proof 
        (define_invariant_command proof_toolkit logic name content)))
val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>invariant'\<close> "Declare an invariant"
    (declare_invariant_parser >> (fn ((logic,name),content) => 
        (define_invariant_command lthy_toolkit logic name content))) *)

  val name_parser = Parse.binding --| Parse.$$$ ":"
  (* TODO: parse program name *)
  val extends_parser = Args.$$$ "extends" |-- Parse.name |> Scan.option
  val range_parser = Args.$$$ "range" |-- tokens_parser
    (Token.keyword_with (fn x => x="pre" orelse x="post"))
  val pre_parser = Args.$$$ "pre" |-- Parse.name |> Scan.option
  val make_post_parser = Parse.name -- tokens_parser (K false)
  val post_parser = Args.$$$ "post" |-- Parse.binding --| Args.$$$ "=" -- make_post_parser
  fun hoare_triple_parser toolkit = name_parser -- extends_parser -- range_parser -- pre_parser -- post_parser
    >> (fn ((((name,extends),range),pre),(post,(make_post,make_post_args))) => 
          (hoare_command toolkit name extends range pre post make_post make_post_args))


fun no_proof_obligation (toolkit:'a toolkit) (command:'a->Proof.state) st = let
  val state = command st
  val finished = state |> Proof.goal |> #goal |> Thm.no_prems
  val _ = if not finished then error "Proof obligations remain. Use hoare'-command instead of hoare-command" else ()
  val st = #qed toolkit state
in st end

fun dummy_proof_obligation (toolkit:'a toolkit) (command:'a->'a) st = let
  val _ = warning "This command never produces proof obligations. Use hoare-command instead of hoare'-command"
  val st = command st
  val state = #theorem toolkit (K I) \<^prop>\<open>PROP x \<equiv> PROP x\<close> st
in state end



(* TODO: add cuts and groups as needed *)
fun command_parser_no_proof toolkit = 
  (Args.$$$ "program" |-- declare_program_parser toolkit) ||
  (Args.$$$ "invariant_has" |-- invariant_has_parser toolkit >> no_proof_obligation toolkit) ||
  (Args.$$$ "config" |-- config_parser toolkit) ||
  (Args.$$$ "invariant" |-- declare_invariant_parser toolkit) ||
  (hoare_triple_parser toolkit >> no_proof_obligation toolkit)

fun command_parser_proof toolkit = 
  (Args.$$$ "program" |-- declare_program_parser toolkit >> dummy_proof_obligation toolkit) ||
  (Args.$$$ "invariant_has" |-- invariant_has_parser toolkit) ||
  (Args.$$$ "config" |-- config_parser toolkit >> dummy_proof_obligation toolkit) ||
  (Args.$$$ "invariant" |-- declare_invariant_parser toolkit >> dummy_proof_obligation toolkit) ||
  (hoare_triple_parser toolkit)

val _ = Outer_Syntax.command \<^command_keyword>\<open>hoare\<close> "Run a Hoare logic command (without proof obligation)"
  (command_parser_no_proof proof_toolkit >> Toplevel.proof)
val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>Hoare\<close> "Run a Hoare logic command (without proof obligation)"
  (command_parser_no_proof lthy_toolkit)
val _ = Outer_Syntax.command \<^command_keyword>\<open>hoare'\<close> "Run a Hoare logic command (with proof obligation)"
  (command_parser_proof proof_toolkit >> Toplevel.proof)
val _ = Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>Hoare'\<close> "Run a Hoare logic command (with proof obligation)"
  (command_parser_proof lthy_toolkit)

end

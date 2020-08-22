structure Forward_Hoare =
struct

local open Utils in

fun name_space_define_with_name context dummy binding value_fun table = let
  val (name,table) = Name_Space.define context false (binding,dummy) table
  val value = value_fun name
  val table = Name_Space.map_table_entry name (K value) table
  in (value,table) end

fun print_with_markup str = (YXML.parse_body str |> \<^print>; str)

val silent = Thread_Data.var () : unit Thread_Data.var
fun tracing' msg = if Thread_Data.get silent = NONE
                   then tracing (msg()) else ()
fun with_silence f x = Thread_Data.setmp silent (SOME()) f x

fun all_to_var maxidx (Const("Pure.all", _) $ Abs (_, T, t)) = 
        subst_bound (Var(("x",Int.max(maxidx, maxidx_of_term t) + 1),T), t)
  | all_to_var _ t = raise TERM("all_to_var", [t])

fun strip_assums_concl_var maxidx (Const("Pure.imp", _) $ _ $ B) = strip_assums_concl_var maxidx B
  | strip_assums_concl_var maxidx (t as Const("Pure.all", _) $ Abs _) =
        strip_assums_concl_var maxidx (all_to_var maxidx t)
  | strip_assums_concl_var _ B = B;

(* Quick but keeps Bound's in term *)
fun bool_of_prop t = 
  if fastype_of t = propT then HOLogic.dest_Trueprop (Logic.strip_assums_concl t)
  else t

(* Replaces Bound's by vars *)
fun bool_of_prop' maxidx t = 
  if fastype_of t = propT then HOLogic.dest_Trueprop (strip_assums_concl_var maxidx t)
  else t



fun string_of_fact_ref (r as Facts.Named _) = Facts.string_of_ref r
  | string_of_fact_ref (Facts.Fact str) = enclose "\<open>" "\<close>" str

fun string_of_fact_ref_attr ctxt (r,attr) =
  string_of_fact_ref r ^
  (Attrib.pretty_attribs ctxt attr |> Pretty.block |> Pretty.string_of)

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
  serial: serial,
  program_term_typ: ex_options -> typ,
  check_program: Proof.context -> term -> unit,
  read_range: ex_options -> ex_range option -> ex_range context_parser,
  pretty_range: Proof.context -> ex_range -> Pretty.T,
  invariant_typ: ex_options -> typ,
  check_invariant: Proof.context -> term -> unit,
  extract_range: Proof.context -> ex_range -> term,
  hoare_thm: Proof.context -> term -> term -> term -> term,
  join_hoare: Proof.context -> term -> ex_range -> term -> ex_range -> term -> thm -> thm -> (ex_range*thm),
  postcondition_generators: (Proof.context -> term -> term -> (term*(Proof.context->tactic)) context_parser) Symtab.table,
  invariant_implication: Proof.context -> term -> term -> term,
  invariant_implication_lhs: term -> term,
  invariant_implication_syntax: Proof.context -> term -> term -> term,
  invariant_parse_translation: Proof.context -> term -> term -> term,
  default_options: ex_options,
  set_option: string -> Input.source -> Proof.context -> morphism -> ex_options -> ex_options,
  subgoal_tactics: (Proof.context -> int -> tactic) Symtab.table,
  invariant_consequences: thm -> Proof.context -> thm list
}


(* val dummy_logic : logic = let fun err _ = error "dummy_logic" in {
  name="",
  program_term_typ = err,
  check_program = err,
  read_range = err,
  pretty_range = err,
  invariant_typ = err,
  check_invariant = err,
  extract_range = err,
  hoare_thm = err,
  join_hoare = err,
  postcondition_generators = Symtab.empty,
  invariant_implication = err,
  invariant_implication_lhs = err,
  invariant_implication_syntax = err,
  invariant_parse_translation = err,
  default_options = Ex_Options (ERROR "dummy_logic"),
  set_option = err,
  subgoal_tactics = Symtab.empty,
  invariant_consequences = err
} end *)

structure LogicTable = Name_Table_Serial(
  type T = logic
  val get_id = #serial
  fun merge _ = raise Same.SAME
)

(* fun name_of_logic ({binding,...}:logic) = Binding.name_of binding *)
(* fun same_logic (l1:logic) (l2:logic) = (#serial l1 = #serial l2) *)

structure Logic_Data = Theory_Data(
  type T = LogicTable.table
  val empty = LogicTable.empty "hoare logic"
  val merge = LogicTable.merge
  val extend = I
)

fun pretty_logic_name ctxt id : string =
  LogicTable.pretty_name_from_id ctxt
    (ctxt |> Proof_Context.theory_of |> Logic_Data.get) id

fun read_logic_name context name : logic = 
  LogicTable.check context (context |> Context.theory_of |> Logic_Data.get) name |> #3

(* fun get_logic thy name = Symtab.lookup (Logic_Data.get thy) name *)
(* fun get_logics thy = Logic_Data.get thy *)
(* fun get_the_logic thy = Name_Space.get (Logic_Data.get thy) *)
(* fun get_logic' ctxt = get_logic (Proof_Context.theory_of ctxt) *)
(* fun get_the_logic' ctxt = get_the_logic (Proof_Context.theory_of ctxt) *)
fun get_logic thy = LogicTable.get_by_id (Logic_Data.get thy)

fun get_the_postcondition_generator context (logic:logic) make_post =
 Symtab.lookup (#postcondition_generators logic) make_post 
 |> the' (fn _ => "Unknown postcondition generator " ^ make_post ^ " in logic " ^ 
                  (#serial logic |> pretty_logic_name (Context.proof_of context)))


type var = string
type program = { serial: serial, code: term, logic: logic }

(* val dummy_program : program = {name="", code=\<^term>\<open>A\<close>, logic=dummy_logic} *)

fun program_morph m ({code,logic,serial}:program) : program = let
  in {logic=logic, serial=serial,
      code = Morphism.term m code} end

(* fun program_eq (p1:program,p2:program) = #serial p1 = #serial p2 *)

type invariant = {
  serial: serial,
  (* name: string, *)
  logic: logic,
  (* binding: binding, *)
  term: term,
  const: term,
  def_thm: thm,
  known_implications: thm list
}

structure InvTable = Name_Table_Serial(
  type T = invariant 
  val get_id = #serial
  fun merge _ = (warning "Merging of invariants not implemented"; raise Same.SAME)
)

(* val dummy_invariant = {name="", logic=dummy_logic, term=\<^term>\<open>A\<close>, const=\<^term>\<open>A\<close>,
  def_thm = @{thm Pure.reflexive}, known_implications=[]} *)

(* fun invariant_eq (i1,i2) = #serial i1 = #serial i2 *)

type hoare = {
  serial: serial,
  logic: logic,
  (* binding: binding, *)
  range: ex_range,
  (* program: string, *)
  (* program_fragment_const: term, *)
  precondition: serial,
  postcondition: serial,
  valid: thm
}

structure HoareTable = Name_Table_Serial(
  type T = hoare 
  val get_id = #serial
  fun merge _ = raise Same.SAME
)

structure ProgTable = Name_Table_Serial(
  type T = program 
  val get_id = #serial
  fun merge _ = raise Same.SAME
)


fun hoare_morphism m ({serial,logic,range,(* program_fragment_const, *)precondition,postcondition,valid}:hoare): hoare = 
  {serial=serial, logic=logic, range=range, 
   (* program_fragment_const = Morphism.term m program_fragment_const, *)
   precondition=precondition, postcondition=postcondition,
   valid = Morphism.thm m valid}

(* fun hoare_eq (h1,h2) = #serial h1 = #serial h2 *)

structure Hoare_Data = Generic_Data (
  type T = { invariants: InvTable.table,
             hoares: HoareTable.table,
             programs: ProgTable.table,
             current_logic: logic option,
             options: ex_options Inttab.table
  }
  val empty = { invariants=InvTable.empty "invariant", hoares=HoareTable.empty "hoare",
    programs=ProgTable.empty "program", current_logic=NONE, options=Inttab.empty }
  fun merge (d1,d2) =
    { invariants = InvTable.merge (#invariants d1, #invariants d2),
      hoares = HoareTable.merge (#hoares d1, #hoares d2),
      programs = ProgTable.merge (#programs d1, #programs d2),
      current_logic = NONE, options = Inttab.empty }
  fun extend {invariants,hoares,programs,current_logic=_,options} =
    {invariants=invariants, hoares=hoares, programs=programs, current_logic=NONE, options=options})

fun map_result map f st = let
  val result_ref = Unsynchronized.ref NONE
  fun f' x = let val (result,y) = f x in (result_ref := SOME result; y) end
  val st = map f' st
  in (the' (fn _ => "map_result: result not assigned") (!result_ref),st) end

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
(* fun add_hoare0 i = map_hoares (Symtab.update_new (Binding.name_of (#binding i), i)) *)
fun add_hoare0decl binding i m context = 
  map_hoares (HoareTable.define context (Morphism.binding m binding, hoare_morphism m i)) context
(* fun get_invariant context name = Symtab.lookup (Hoare_Data.get context |> #invariants) name *)
(* fun get_invariants context = Hoare_Data.get context |> #invariants *)
fun get_invariant_by_id context = 
  InvTable.get_by_id (Hoare_Data.get context |> #invariants)
(* get_invariant context name |> the' (fn _ => "Unknown invariant " ^ name) *)
fun get_hoare_by_id context id = HoareTable.get_by_id (Hoare_Data.get context |> #hoares) id
(* fun get_the_hoare context name = get_hoare context name |> the' (fn _ => "Unknown Hoare judgment " ^ name) *)
(* fun get_program_internal context name = Name_Space.lookup (Hoare_Data.get context |> #programs) name *)
fun get_program_by_id context id = ProgTable.get_by_id (Hoare_Data.get context |> #programs) id
fun get_program_by_name context name = ProgTable.get_by_name (Hoare_Data.get context |> #programs) name
fun get_program_name_by_id context id = ProgTable.get_name_by_id (Hoare_Data.get context |> #programs) id
(* fun get_the_program_internal context name = get_program_internal context name |> the' (fn _ => "Unknown program " ^ name) *)
fun get_current_logic context = Hoare_Data.get context |> #current_logic
fun get_the_current_logic context = get_current_logic context |> the' (fn _ => "No current logic")
fun map_known_implications f ({known_implications,serial,const,def_thm,logic,term} : invariant) : invariant =
  {known_implications = f known_implications,serial=serial,const=const,def_thm=def_thm,logic=logic,term=term}

fun pretty_program_name ctxt id : string = 
  ProgTable.pretty_name_from_id ctxt
    (ctxt |> Context.Proof |> Hoare_Data.get |> #programs) id

fun read_program_name context name : program = 
  ProgTable.check context (context |> Hoare_Data.get |> #programs) name |> #3
fun read_program_name_as_name context name : string = 
  ProgTable.check context (context |> Hoare_Data.get |> #programs) name |> #1

fun pretty_invariant_name ctxt id : string = 
  InvTable.pretty_name_from_id ctxt
    (ctxt |> Context.Proof |> Hoare_Data.get |> #invariants) id

fun read_invariant_name context name : invariant = 
  InvTable.check context (context |> Hoare_Data.get |> #invariants) name |> #3

fun read_hoare_name context name : hoare = 
  HoareTable.check context (context |> Hoare_Data.get |> #hoares) name |> #3

structure Hoare_Proof_Data = Proof_Data (
  (* current_invariant is local to a proof obligation created by a hoare' command *)
  type T = { current_invariant: invariant option }
  fun init _ = { current_invariant=NONE }
)


fun get_options (logic:logic) context = 
  case Inttab.lookup (Hoare_Data.get context |> #options) (#serial logic) of 
    SOME options => options
  | NONE => #default_options logic

fun set_option (logic:logic) name content m context = let
  val ctxt = Context.proof_of context
  val options = get_options logic context
  val options = #set_option logic name content ctxt m options
  val context = map_options (Inttab.update (#serial logic, options)) context
  in context end



fun set_current_invariant invariant = Hoare_Proof_Data.map (fn
  { current_invariant=_ } => { current_invariant = SOME invariant })
fun get_current_invariant ctxt = Hoare_Proof_Data.get ctxt |> #current_invariant
val get_the_current_invariant = get_current_invariant
  #> the' (fn _ => "No current invariant")
val get_current_invariant_def = get_current_invariant #> Option.map #def_thm
val get_the_current_invariant_def = get_current_invariant_def
  #> the' (fn _ => "No current invariant")

fun invariant_morph m ({serial,logic,term,const,def_thm,known_implications}:invariant) : invariant =
 {serial=serial, logic=logic, term=Morphism.term m term,
   const=Morphism.term m const, def_thm=Morphism.thm m def_thm, 
   known_implications=map (Morphism.thm m) known_implications}

fun catch_internal_error logic what f x = f x
   handle TYPE (msg, Ts, ts) => 
   raise TYPE ("Internal error " ^ what() ^ " (logic " ^ logic() ^ "): " ^ msg, Ts, ts)
   handle ERROR msg => 
   raise ERROR ("Internal error " ^ what() ^ " (logic " ^ logic() ^ "): " ^ msg)


fun add_known_implication (invariant:invariant) (implication:thm) context : Context.generic = let
  (* val context = #context toolkit st *)
  (* val invariant = get_the_invariant context invariant_name *)
  val logic = #logic invariant
  val const = #invariant_implication_lhs logic (implication |> Thm.prop_of |> bool_of_prop)
  val _ = if const = #const invariant then ()
          else raise THM ("add_known_implication: implication incorrect for invariant "^ pretty_invariant_name (Context.proof_of context) (#serial invariant), 
                          1, [implication])
(*   fun update m = let
    val implication' = Morphism.thm m implication
    in map_invariants (Symtab.map_entry invariant_name (map_known_implications 
            (fn is => implication'::is))) end
  val st = #declaration toolkit update st *)
in map_invariants (InvTable.map_entry (#serial invariant) (map_known_implications 
            (fn is => implication::is))) context end

fun declare_invariant_consequences (toolkit:'a toolkit) (logic:logic) (invariant:invariant) (st:'a) = let
  val ctxt = #context toolkit st |> Context.proof_of
  val conseqs = #invariant_consequences logic (#def_thm invariant) ctxt
  val _ = if not (null conseqs) then 
               (tracing' (fn _ => "Registering consequences:");
               tracing' (fn _ => conseqs |> map (fn thm => Syntax.pretty_term ctxt (Thm.prop_of thm))
                            |> Pretty.commas |> Pretty.block |> Pretty.string_of))
          else ()
  fun declare conseq st = let 
    val st = #note toolkit Binding.empty conseq st
    val st = #declaration toolkit (fn m => add_known_implication invariant (Morphism.thm m conseq)) st
    in st end
  val st = fold declare conseqs st
  in st end

fun add_invariant (toolkit:'st toolkit) (logic:logic) binding (invariant:term) st : invariant * 'st = let
  fun bind suffix = Binding.suffix_name suffix binding
  val (invariant_const,thm,st) = 
      #define toolkit (bind "_inv") (bind "_inv_def") invariant st
      (* def' (bind "_inv") invariant ctxt *)
  val invariant : invariant = 
        {serial = serial(), logic = logic,
         const = invariant_const, term = invariant, 
         def_thm = thm, 
         known_implications=[]}
(*  fun add_invariant0 i = map_invariants (Symtab.update_new (Binding.name_of (#binding i), i)) *)
  val st = #declaration toolkit (fn m => fn context => 
    map_invariants (InvTable.define
      context (Morphism.binding m binding, invariant_morph m invariant)) context) st
  in (invariant, st) end

fun parse_src expect ctxt (parser:'a context_parser) (src:Token.src) : 'a = let
  val eof = Parse.group expect Parse.eof |> Scan.lift
  val (result,_) = Scan.catch (parser --| eof) (Context.Proof ctxt, src @ [Token.eof])
  in result end

fun join_hoare (toolkit:'a toolkit) binding (hoare1:serial) (hoare2:serial) (st:'a) = let
  val context = #context toolkit st
  val ctxt = Context.proof_of context
  val hoare1' = get_hoare_by_id context hoare1
  val hoare2' = get_hoare_by_id context hoare2
  (* val program = #program hoare1' *)
  (* val _ = if #program hoare1' <> #program hoare2' then error "mismatch" else () *)
  val _ = if #serial (#logic hoare1') = #serial (#logic hoare2') then () 
          else error "mismatch"
  val _ = if #postcondition hoare1' <> #precondition hoare2' then 
          error "mismatch" else ()
  (* val program' = program |> get_the_program context *)
  (* val logic = program' |> #logic |> get_the_logic' ctxt *)
  val a = hoare1' |> #precondition |> get_invariant_by_id context |> #const
  val b = hoare1' |> #postcondition |> get_invariant_by_id context |> #const
  val c = hoare2' |> #postcondition |> get_invariant_by_id context |> #const
  val logic = #logic hoare1'
  val (range,joined_thm) = 
          catch_internal_error (fn _ => pretty_logic_name ctxt (#serial logic)) (fn _ => "invoking join_hoare") 
          (#join_hoare logic ctxt a (#range hoare1') b (#range hoare2') c
           (#valid hoare1')) (#valid hoare2')
  (* val program_fragment = (#extract_range logic) ctxt range *)
(*   val (program_fragment_const,_,st) = 
      #define toolkit (Binding.suffix_name "_prog" binding) (Binding.suffix_name "_prog_def" binding) program_fragment st *)

  val st = #note toolkit (Binding.suffix_name "_valid" binding) joined_thm st

  val info : hoare = {serial=serial(), range=range,
    precondition= #precondition hoare1',
    postcondition= #postcondition hoare2',
    (* program_fragment_const=program_fragment_const, *)
    logic = logic,
    (* program=program, *)
    valid = joined_thm
  }
  
  val st = #declaration toolkit (add_hoare0decl binding info) st

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


fun read_term_typed ctxt T str = let
  val raw_term = Syntax.parse_term ctxt str
  val typed = Const("_type_constraint_", T --> T) $ raw_term
  val t = Syntax.check_term ctxt typed
  in t end

fun set_current_logic_command (toolkit:'a toolkit) (logic:logic) st = let
  val _ = tracing' (fn _ => "Setting current logic to " ^ pretty_logic_name 
            (#context toolkit st |> Context.proof_of) (#serial logic))
  in #declaration toolkit (K (set_current_logic logic)) st end

fun define_program_command (toolkit:'a toolkit) (logic:string*Position.T) binding content (st:'a) : 'a = let
val _ = print_with_markup content
  val context = #context toolkit st
  val ctxt = Context.proof_of context
  (* val thy = Context.theory_of context *)
  val logic = read_logic_name context logic
  val options = get_options logic context
  val program = read_term_typed ctxt (#program_term_typ logic options) content
  val _ = #check_program logic ctxt program
  val st = set_current_logic_command toolkit logic st
  val (_,_,st) = #define toolkit binding (Binding.suffix_name "_def" binding) program st
  (* val name = Binding.name_of binding *)
  val prog = {serial = serial(), logic=logic, code=program}
  fun add_program0decl (m:morphism) context = let
    (* val prog : program = {logic=logic, code=program} *)
    val context = map_programs (ProgTable.define context
      (Morphism.binding m binding, program_morph m prog)) context 
    val name = get_program_name_by_id context (#serial prog)
    val context = set_option logic "@last_program" (Input.string name) m context
    in context end
  val st = #declaration toolkit add_program0decl st
in st end

fun set_option_command (toolkit:'a toolkit) (logic:string*Position.T) name content (st:'a) : 'a = let
  val context = #context toolkit st
  (* val ctxt = Context.proof_of context *)
  (* val thy = Context.theory_of context *)
  val logic = read_logic_name context logic
  val st = set_current_logic_command toolkit logic st
  val st = #declaration toolkit (set_option logic name (Syntax.read_input content)) st
in st end

fun define_invariant_command (toolkit:'a toolkit) logic name content (st:'a) : 'a = let 
  val context = #context toolkit st
  val ctxt = Context.proof_of context
  val logic = read_logic_name context logic
  val options = get_options logic context
  val term = read_term_typed ctxt (#invariant_typ logic options) content
  val _ = #check_invariant logic ctxt term
  val _ = tracing ("Declaring invariant "^ string_of_binding_invariant name ^ " in logic " ^ 
                  pretty_logic_name ctxt (#serial logic))
  val st = set_current_logic_command toolkit logic st
  val (invariant,st) = add_invariant toolkit logic name term st
  val st = declare_invariant_consequences toolkit logic invariant st
in st end

fun tokens_parser stop : Token.src parser = Scan.many (fn tok => not (stop tok orelse Token.is_eof tok orelse Token.is_error tok))


(* fun invariant_has_command (toolkit:'a toolkit) (binding:binding) (invariant:string) (term:string) (st:'a) : Proof.state = let
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
in state end *)

fun maybe_OF thm thms : thm option =
  SOME (thm OF thms) handle THM _ => NONE

fun filter_OF (thms1:thm list) (thms2:thm list) : thm list = 
  thms1 |> map_filter (fn thm => maybe_OF thm thms2)

(* fun filter_inst ctxt (thms:thm list) var value : thm list =
  thms |> map_filter (fn thm' => SOME (Drule.infer_instantiate ctxt [(var,value)] thm') handle THM _ => NONE) *)

(* Raises TERM or TYPE if not found *)
fun get_invariant_from_implication' (context:Context.generic) (logic:logic) (t:term) = let
  val const = #invariant_implication_lhs logic (bool_of_prop t)
  val inv = case context |> Hoare_Data.get |> #invariants |> InvTable.get_first 
(* TODO: discard invariants from a different logic *)
                   (fn inv => if #const inv = const then SOME inv else NONE)
            of SOME inv => inv | NONE => raise TERM("get_invariant_from_implication'", [t,const])
in inv end

(* fun name_space_get_first (f:string*'a->'b option) (table:'a Name_Space.table) = let
  exception Found of 'b
  fun check (name,x) () = case f (name,x) of NONE => () | SOME y => raise Found y
  val found = (Name_Space.fold_table check table (); NONE)
              handle Found x => SOME x
  in found end *)

(* TODO: rewrite: we don't need to loop over logics separately since invariants carry the logic *)
fun get_invariant_from_implication (context:Context.generic) (t:term) = let
  val inv = Logic_Data.get (Context.theory_of context) |> LogicTable.get_first
    (fn logic => SOME (get_invariant_from_implication' context logic t)
        handle TERM _ => NONE | TYPE _ => NONE | Match => NONE)
  in inv |> the' (fn _ => "Could not identify invariant in the lhs of " ^ 
                        Syntax.string_of_term (Context.proof_of context) t) end

fun add_known_implication_auto (implication:thm) context : Context.generic = let
  (* val ctxt = Context.proof_of context *)
  val invariant = get_invariant_from_implication context (Thm.prop_of implication)
  val context = add_known_implication invariant implication context
  in context end

val _ = Theory.setup
  (Attrib.setup \<^binding>\<open>hoare_invi\<close> 
    (Scan.succeed (Thm.declaration_attribute add_known_implication_auto))
    "Declares this theorem as an invariant implication")

fun auto_subgoal_tac lenient (logic:logic) ctxt = SUBGOAL (fn (t,i) => case t of
  Const(\<^const_name>\<open>SOLVE_WITH\<close>,_) $ str $ _ => let
    val str = HOLogic.dest_literal str
    val (str,typ) = case String.sub (str,size str-1) of
                        #"?" => (String.substring (str,0,size str-1), #"?")
                      | _ => (str ,#" ")
    val lenient = case typ of #"?" => true | #" " => lenient | _ => raise Match
    val tac = case str of 
                _ => case Symtab.lookup (#subgoal_tactics logic) str of
                       SOME tac => tac ctxt
                      | NONE => raise TERM("auto_subgoal_tac: unknown tactic "^str^" for logic "^ 
                                pretty_logic_name ctxt (#serial logic), [t])
    val try = if lenient then fn tac => fn i => TRY (tac i) else I
    in (resolve_tac ctxt @{thms remove_SOLVE_WITH} THEN' 
        try (tac THEN_ALL_NEW auto_subgoal_tac lenient logic ctxt)) i end
  | _ => all_tac)

fun current_invariant_tac lenient OFs thms (ctxt:Proof.context) = SUBGOAL (fn (t,i) => let
  val thms = thms ctxt
  val inv = case get_current_invariant ctxt of SOME inv => inv
              | NONE => let
                  val t = bool_of_prop t handle TERM(msg,Ts) => raise TERM("current_invariant_tac: "^msg,Ts)
                  in get_invariant_from_implication (Context.Proof ctxt) t end
  val logic = #logic inv
  val inv_def = #def_thm inv
  val inv_markup_name = pretty_invariant_name ctxt (#serial inv)
  val thms_inst = filter_OF thms [inv_def]
  val _ = tracing' (fn _ => "Available rules for invariant " ^ inv_markup_name ^ ":")
  val _ = if null OFs then () else tracing' (fn _ => "([\<star>] marks rules that can be instantiated with current facts)")
  val thms_inst = map_filter (fn thm => let
    val thm' = maybe_OF thm OFs
    val _ = tracing' (fn _ => let
        val thm_str = thm |> Thm.prop_of |> Syntax.pretty_term ctxt
        val thm_str = if null OFs orelse is_none thm'
                      then [thm_str] |> Pretty.item |> Pretty.string_of
                      else [Pretty.str "[\<star>] ", thm_str] |> Pretty.item |> Pretty.string_of
        in thm_str end)
    in thm' end) thms_inst
  val _ = if null thms_inst 
          then error ("No rules found that match invariant " ^ inv_markup_name) else ()
  in
    (resolve_tac ctxt thms_inst
     THEN_ALL_NEW
     auto_subgoal_tac lenient logic ctxt) i
  end)

(* The SUBGOAL is to avoid that error_tac already throws an error when run on the dummy fact _ *)
fun error_tac msg = SUBGOAL (fn _ => error (msg ())) 1

fun invariant_untouched_tac ctxt lenient previous = current_invariant_tac lenient [previous] 
  (fn _ => Named_Theorems.get ctxt \<^named_theorems>\<open>hoare_untouched\<close>) ctxt
fun invariant_untouched_method lenient ctxt = METHOD (
      fn [fact] => invariant_untouched_tac ctxt lenient fact 1
       | facts => error_tac (fn _ => "untouched method expects exactly one fact (the previous invariant implication), not " ^ string_of_int (length facts)))

fun invariant_wp_tac ctxt lenient = current_invariant_tac lenient [] 
  (fn ctxt => Named_Theorems.get ctxt \<^named_theorems>\<open>hoare_wp\<close>) ctxt


val _ = Theory.setup
  (Attrib.setup \<^binding>\<open>current_invariant_def\<close> 
  (Scan.succeed (Thm.rule_attribute [] (fn context => fn _ =>
    case Context.proof_of context |> get_current_invariant_def of
      NONE => Drule.dummy_thm
    | SOME thm => thm)))
    "[[current_invariant_def]] gives the definition of the currently investigated invariant)")


fun preserve_invariant_implication ctxt implication (new_invariant:invariant) = let
  val ii1 = implication
  val logic = #logic new_invariant
  val inv2 = new_invariant |> #const
  val ii2 = #invariant_implication_syntax logic ctxt inv2 (Var(("inv2",0),dummyT))
            |> Syntax.check_term (Proof_Context.set_mode Proof_Context.mode_schematic ctxt)
            |> HOLogic.mk_Trueprop
  fun tac {context,...} = invariant_untouched_tac context false ii1 1
  in Goal.prove ctxt [] [] ii2 tac end

fun auto_preserve_invariant_implications (toolkit:'a toolkit) implications (new_invariant:invariant) (st:'a) : 'a = let
  val ctxt = #context toolkit st |> Context.proof_of
  fun try1 implication st = let 
    val _ = tracing ("Trying to preserve: " ^ Syntax.string_of_term ctxt (Thm.prop_of implication))
    val new_impl = SOME (with_silence (preserve_invariant_implication ctxt implication) new_invariant)
                   handle ERROR _ => NONE | TERM _ => NONE | THM _ => NONE | TYPE _ => NONE | Match => NONE
    val st = case new_impl of 
      NONE => (tracing "   \<dots> failed"; st)
      | SOME new_impl => let
        val _ = tracing ("   \<dots> success: " ^ Syntax.string_of_term ctxt (Thm.prop_of new_impl))
        val st = #note toolkit Binding.empty new_impl st
        val st = #declaration toolkit (fn m => add_known_implication new_invariant (Morphism.thm m new_impl)) st
        in st end
    in st end
  val st = fold try1 implications st
in st end


fun new_hoare (toolkit:'a toolkit) binding after_qed0 (logic:logic) range (precondition:serial) (postcondition:serial) (st:'a) : Proof.state = let
  val context = #context toolkit st
  val ctxt = Context.proof_of context
  (* val program = get_the_program context program *)
  val precondition = get_invariant_by_id context precondition
  val postcondition = get_invariant_by_id context postcondition
  (* fun bind suffix = Binding.suffix_name suffix binding *)
  (* val logic = get_the_logic (Context.theory_of context) (#logic program) *)
(*   val _ = if #valid_range logic range then ()
          else error ("Invalid range " ^ Pretty.string_of (#pretty_range logic ctxt range)) *)
  val program_fragment = (#extract_range logic) ctxt range
  val _ = tracing ("Range: " ^ (Pretty.string_of (#pretty_range logic ctxt range)))
  val _ = tracing ("Program fragment: " ^ Syntax.string_of_term ctxt program_fragment)
(*   val (program_fragment_const,_,st) = 
      #define toolkit (bind "_prog") (bind "_prog_def") program_fragment st *)
  val valid_prop = #hoare_thm logic ctxt (#const precondition) program_fragment (#const postcondition)
  fun after_qed valid st = let
      val info : hoare = {serial=serial(), range=range,
        precondition = #serial precondition,
        postcondition = #serial postcondition,
        (* program_fragment_const=program_fragment_const, *)
        logic = logic,
        (* program=program |> #binding |> Binding.name_of, *)
        valid=valid}
      val st = #note toolkit (Binding.suffix_name "_valid" binding) valid st
      val st = #declaration toolkit (add_hoare0decl binding info) st
      val st = auto_preserve_invariant_implications toolkit
                (#known_implications precondition) postcondition st
      in after_qed0 (st, info) end
  val state = toolkit_theorem toolkit after_qed valid_prop st

in state end



fun new_hoare_auto (toolkit:'a toolkit) binding after_qed0 (logic:logic) range (precondition:serial) 
    (postcondition:binding) (make_post:string) (make_post_args:Token.src) (st:'a) : Proof.state = let
  val context = #context toolkit st
  val ctxt = Context.proof_of context
  val program_fragment = (#extract_range logic) ctxt range
  val precondition' = get_invariant_by_id context precondition
  val make_post' = get_the_postcondition_generator context logic make_post ctxt program_fragment (#const precondition')
  val (post,tac) = parse_src (fn _ =>  "end of arguments to " ^ make_post) ctxt make_post' make_post_args
  val _ = catch_internal_error (fn _ => pretty_logic_name ctxt (#serial logic))
            (fn _ => "typechecking result of postcondition generator "^make_post)
            (Sign.cert_term (Proof_Context.theory_of ctxt)) post
  val (post,st) = add_invariant toolkit logic postcondition post st
  val state = new_hoare toolkit binding after_qed0 logic range precondition (#serial post) st
  val state = Proof.apply (Method.Basic (Method.unfold [#def_thm post]), Position.no_range) state
    |> ensure_result (K "could not unfold definition of postcondition (internal error)")
  (* fun tac' ctxt = tac ctxt THEN ALLGOALS (auto_subgoal_tac false logic ctxt) *)
  val state = Seq.maps (Proof.apply (Method.Basic (fn ctxt => SIMPLE_METHOD (tac ctxt)), Position.no_range)) state
    |> ensure_result (fn _ => "Could not apply tactic associated with postcondition " ^ make_post)
  val state = Seq.maps (Proof.apply (Method.Basic (fn ctxt => SIMPLE_METHOD (ALLGOALS (auto_subgoal_tac false logic ctxt))), Position.no_range)) state
    |> ensure_result (fn _ => "Could not solve subgoals of tactic associated with postcondition " ^ make_post)

  in Seq.hd state end


fun extend_hoare_auto (toolkit:'a toolkit) binding (previous:serial) after_qed0 range (postcondition:binding)
    (make_post:string) (make_post_args:Token.src) (st:'a) = let
  val context = #context toolkit st
  val binding_step = Binding.suffix_name "_step" binding
  val previous_hoare = get_hoare_by_id context previous
  val logic = #logic previous_hoare
  val precondition = #postcondition previous_hoare
  fun after_qed (st, hoare) = let
    val (st, joined_hoare) = 
      join_hoare toolkit binding previous (#serial hoare) st
    in after_qed0 (st, hoare, joined_hoare) end
  val state = new_hoare_auto toolkit binding_step after_qed logic range precondition postcondition make_post make_post_args st
in state end

fun hoare_command (toolkit:'a toolkit) (name:binding) (extends:(string*Position.T) option) (range:Token.src) (pre:(string*Position.T) option) (post:binding)
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
             | SOME pre => let 
                val pre = read_invariant_name context pre |> #serial
                in new_hoare_auto toolkit name fst logic range' pre post make_post make_post_args st end)
    | SOME previous => let
        val previous = read_hoare_name context previous |> #serial
        in extend_hoare_auto toolkit name previous #1 range' post make_post make_post_args st end
  in state end

fun preserve_command (toolkit:'a toolkit) invs (in_inv:string*Position.T) (state:'a) = let
  val ctxt = #context toolkit state |> Context.proof_of
  fun one (binding, thm_ref) state = let
    val thm_ref_str = string_of_fact_ref_attr ctxt thm_ref
    val _ = tracing ("Processing " ^ thm_ref_str)
    val thm = case Attrib.eval_thms ctxt [thm_ref] of [thm] => thm
                | _ => error ("Fact "^thm_ref_str^" consists of more than one theorem")
    val inv2 = read_invariant_name (Context.Proof ctxt) in_inv
    val ii2 = preserve_invariant_implication ctxt thm inv2
    val state = #note toolkit binding ii2 state
  in state end
in fold one invs state end

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
    val (inv1_name,constr) = case inv1_var of Const(\<^syntax_const>\<open>_constrain\<close>,_) $ Free(n,_) $ constr => (n,constr)
                         | Free(n,_) => (n,@{const Pure.dummy_pattern(dummy)})
                         | _ => raise TERM("_invariant_implication parse_translation 1", [inv1_var,inv2])
    val pos = case Term_Position.decode_position constr of NONE => Position.none
                  | SOME (p, _) => p
    val inv1 = read_invariant_name (Context.Proof ctxt) (inv1_name,pos)
    val logic = #logic inv1
    val inv1_const = #const inv1 |> mark_atoms
    val inv2_tr = inv2 |> #invariant_parse_translation logic ctxt (#const inv1)
    val impl = #invariant_implication_syntax logic ctxt inv1_const inv2_tr
  in impl end
  | invariant_implication_tr _ ts = raise TERM("invariant_implication_tr", ts)



(** Isar command **)

val binding_parser = Parse.binding --| Args.$$$ ":"

val logic_parser = Parse.$$$ "(" |-- Parse.name_position --| Parse.$$$ ")"
fun declare_program_parser toolkit = (logic_parser -- binding_parser -- Parse.term)
  >> (fn ((logic,name),content) => define_program_command toolkit logic name content)

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

val name_parser = Parse.binding --| Args.colon
val extends_parser = Args.$$$ "extends" |-- Parse.name_position |> Scan.option
val range_parser = Args.$$$ "range" |-- tokens_parser
  (Token.keyword_with (fn x => x="pre" orelse x="post"))
val pre_parser = Args.$$$ "pre" |-- Parse.name_position |> Scan.option
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
  val state = toolkit_theorem toolkit (K I) \<^prop>\<open>PROP x \<equiv> PROP x\<close> st
in state end


fun preserve_command_parser toolkit = 
  (Parse.and_list1 (Scan.optional name_parser Binding.empty -- Parse.thm)
       -- (Parse.$$$ "in" |-- Parse.name_position))
  >> (fn (impls,in_inv) => preserve_command toolkit impls in_inv)

(* TODO: add cuts and groups as needed *)
fun command_parser_no_proof toolkit = 
  (Args.$$$ "program" |-- declare_program_parser toolkit) ||
  (* (Args.$$$ "invariant_has" |-- invariant_has_parser toolkit >> no_proof_obligation toolkit) || *)
  (Args.$$$ "config" |-- config_parser toolkit) ||
  (Args.$$$ "invariant" |-- declare_invariant_parser toolkit) ||
  (Args.$$$ "preserve" |-- preserve_command_parser toolkit) ||
  (hoare_triple_parser toolkit >> no_proof_obligation toolkit)

fun command_parser_proof toolkit = 
  (Args.$$$ "program" |-- declare_program_parser toolkit >> dummy_proof_obligation toolkit) ||
  (* (Args.$$$ "invariant_has" |-- invariant_has_parser toolkit) || *)
  (Args.$$$ "config" |-- config_parser toolkit >> dummy_proof_obligation toolkit) ||
  (Args.$$$ "invariant" |-- declare_invariant_parser toolkit >> dummy_proof_obligation toolkit) ||
  (Args.$$$ "preserve" |-- preserve_command_parser toolkit >> dummy_proof_obligation toolkit) ||
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
end
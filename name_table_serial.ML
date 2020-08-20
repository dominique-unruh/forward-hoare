functor Name_Table_Serial(Config: sig 
  type T
  val get_id : T -> serial
  (* Can raise Same.SAME or ERROR *)
  val merge : T * T -> T
end) : sig
  type T = Config.T
  type table
  val empty : string -> table
  val define : Context.generic -> (binding * Config.T) -> table -> table
  val merge : table * table -> table
  val get_id : Config.T -> serial
  val get_by_id : table -> serial -> T
  val get_by_name : table -> string -> T
  val get_name_by_id : table -> serial -> string
  val pretty_name : Proof.context -> table -> string -> string
  val pretty_name_from_id : Proof.context -> table -> serial -> string
  val check : Context.generic -> table -> (xstring*Position.T) -> string * serial * T
  val map_entry : serial -> (T -> T) -> table -> table
  val get_first: (T -> 'a option) -> table -> 'a option
end = struct
type T = Config.T
val get_id = Config.get_id
type table = {name_table: serial Name_Space.table, entry_table: (T*string) Inttab.table}
fun empty name : table = {name_table = Name_Space.empty_table name, 
                                    entry_table = Inttab.empty}
fun define context (binding,entry) ({name_table,entry_table}:table) : table = let
  val id = get_id entry
  val (name,name_table) = Name_Space.define context false (binding,id) name_table
  val entry_table = Inttab.update_new (id,(entry,name)) entry_table
  in {name_table=name_table,entry_table=entry_table} end
fun merge_entry name_space _ ((entry1,name1), (entry2,name2)) =
     if name1 <> name2 then error ("When joining name space '"^ Name_Space.kind_of (Name_Space.space_of_table name_space) ^"': mismatch of names "^name1^" vs "^name2^" for same id")
     else (Config.merge (entry1,entry2), name1)
          handle ERROR msg => raise ERROR ("Cannot merge entry "^name1^" in table " ^ Name_Space.kind_of (Name_Space.space_of_table name_space) ^ ": " ^ msg)
fun merge (table1:table, table2:table) : table =
  {name_table = Name_Space.merge_tables (#name_table table1, #name_table table2),
   entry_table = Inttab.join (merge_entry (#name_table table1)) (#entry_table table1, #entry_table table2)}
fun kind_of table = Name_Space.kind_of (Name_Space.space_of_table (#name_table table))
fun get_both_by_id (table:table) id : T * string = case Inttab.lookup (#entry_table table) id of
  NONE => error ("No " ^ kind_of table ^ " with id " ^ string_of_int id ^ " found")
  | SOME result => result
fun get_by_id table id = get_both_by_id table id |> fst
fun get_name_by_id table id = get_both_by_id table id |> snd
fun get_by_name table name = get_by_id table (Name_Space.get (#name_table table) name)
fun pretty_name ctxt table name = Name_Space.pretty ctxt (#name_table table |> Name_Space.space_of_table) name |> Pretty.string_of
fun pretty_name_from_id ctxt table id = pretty_name ctxt table (get_name_by_id table id)
fun check context table (xname,pos) = let
  (* val source : Input.source = Syntax.read_input str *)
  (* val pos = Input.pos_of source *)
  (* val xname = Input.text_of source *)
  val (name,id) = Name_Space.check context (#name_table table) (xname,pos)
  (* val _ = \<^print>(str,source,pos,xname,name,id) *)
  val entry = get_by_id table id
  in (name,id,entry) end
fun map_entry id f {name_table, entry_table} =
  {name_table=name_table, entry_table=Inttab.map_entry id (apfst f) entry_table}
fun get_first (f:T->'a option) table : 'a option =
  Inttab.get_first (fn (_,(x,_)) => f x) (#entry_table table)
end

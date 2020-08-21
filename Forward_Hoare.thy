theory Forward_Hoare
  imports Main
  keywords
        "hoare" :: prf_decl % "proof"
    and "hoare'" :: prf_goal % "proof"
    and "Hoare" :: thy_decl
    and "Hoare'" :: thy_goal

    and "range" "pre" "post" "extends" "program" "invariant_has" "config" "invariant" "preserve"
begin

named_theorems hoare_untouched
named_theorems hoare_wp

definition SOLVE_WITH :: "String.literal \<Rightarrow> prop \<Rightarrow> prop" 
  where "SOLVE_WITH _ == \<lambda>x. x"
declare SOLVE_WITH_def[simp]

ML \<open>
fun dest_bit_syntax (Const(\<^const_syntax>\<open>False\<close>,_)) = 0
  | dest_bit_syntax (Const(\<^const_syntax>\<open>True\<close>,_)) = 1
  | dest_bit_syntax _ = raise TERM ("dest_bit", []);

val dest_bits_syntax = Integer.eval_radix 2 o map dest_bit_syntax;

val dest_literal_syntax =
  let
    fun dest (Const (\<^const_syntax>\<open>Groups.zero_class.zero\<close>, Type ("String.literal", []))) = []
      | dest (Const (\<^const_syntax>\<open>String.empty_literal\<close>, _)) = []
      | dest (Const (\<^const_syntax>\<open>String.Literal\<close>, _) $ b0 $ b1 $ b2 $ b3 $ b4 $ b5 $ b6 $ t) =
          chr (dest_bits_syntax [b0, b1, b2, b3, b4, b5, b6]) :: dest t
      | dest t = raise TERM ("dest_literal", [t]);
  in implode o dest end;
\<close>


syntax "_SOLVE_WITH" :: "id \<Rightarrow> prop \<Rightarrow> prop" ("\<lbrakk>SOLVER _\<rbrakk> _" 0)
syntax "_SOLVE_WITH_opt" :: "id \<Rightarrow> prop \<Rightarrow> prop" ("\<lbrakk>SOLVER _?\<rbrakk> _" 0)

parse_translation \<open>[
  (\<^syntax_const>\<open>_SOLVE_WITH\<close>, fn ctxt => fn [Free(n,_), t] =>
    Const(\<^const_name>\<open>SOLVE_WITH\<close>, dummyT) $ HOLogic.mk_literal n $ t),
  (\<^syntax_const>\<open>_SOLVE_WITH_opt\<close>, fn ctxt => fn [Free(n,_), t] =>
    Const(\<^const_name>\<open>SOLVE_WITH\<close>, dummyT) $ HOLogic.mk_literal (n ^ "?") $ t)]\<close>

print_translation \<open>[(\<^const_syntax>\<open>SOLVE_WITH\<close>, fn ctxt => fn [n,t] => let
    val n' = dest_literal_syntax n handle TERM _ => raise Match
    val (n',const) = case String.sub (n',size n'-1) of
                        #"?" => (String.substring (n',0,size n'-1),\<^syntax_const>\<open>_SOLVE_WITH_opt\<close>)
                      | _ => (n',\<^syntax_const>\<open>_SOLVE_WITH\<close>)
    in Const(const,dummyT) $ Free(n',dummyT) $ t end)]\<close>

lemma remove_SOLVE_WITH: "PROP P \<Longrightarrow> PROP SOLVE_WITH s PROP P"
  unfolding SOLVE_WITH_def by auto

ML_file "name_table_serial.ML"
ML_file "forward_hoare.ML"
ML_file "forward_hoare_utils.ML"
ML_file "hoare_logic.ML"


method_setup untouched =
  \<open>Scan.lift (Scan.optional (Parse.reserved "lax" >> K true) false)
    >> Forward_Hoare.invariant_untouched_method\<close> 
  "Invariant is preserved"

method_setup wp =
  \<open>Scan.lift (Scan.optional (Parse.reserved "lax" >> K true) false)
    >> (fn lenient => fn ctxt => SIMPLE_METHOD' (Forward_Hoare.invariant_wp_tac ctxt lenient))\<close>
  "Weakest precondition"

syntax "_invariant_implication" :: "id_position \<Rightarrow> 'a \<Rightarrow> bool" ("{_ \<Rightarrow> _}")
parse_translation \<open>[
  (\<^syntax_const>\<open>_invariant_implication\<close>, Forward_Hoare.invariant_implication_tr)]\<close>


end

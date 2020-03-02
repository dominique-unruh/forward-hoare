theory Test_Reorder_Hoare
  imports Reorder_Hoare
begin

ML \<open>
Reorder_Hoare.swap_instructions \<^context> \<^term>\<open>INSTR[x := $z+3]\<close> \<^term>\<open>INSTR[y := $w*10]\<close>
\<close>

ML \<open>
Reorder_Hoare.insert_into_ordered \<^context> (3,\<^term>\<open>INSTR[x:=1]\<close>) ([2,4],\<^term>\<open>PROG[y:=2;x:=3]\<close>)
  |> (fn (ns,is,thm) => (ns, Thm.cterm_of \<^context> is, thm))
\<close>

ML \<open>
Reorder_Hoare.sort_program \<^context> ([1,2,0], \<^term>\<open>PROG[x := 1; x := 2; z := 3]\<close>)
  |> (fn (ns,is,thm) => (ns, Thm.cterm_of \<^context> is, thm))
\<close>


ML \<open>
Reorder_Hoare.append_conv \<^cterm>\<open>[1,2,3]@[4,5,6]\<close>
\<close>


Hoare program (reorder_hoare) prog: \<open>PROG[x:=1; y:=1; z:=1]\<close>

lemma True
proof

  invariant (reorder_hoare) start: "\<lambda>m. True"

  hoare step1: range 1 pre start post step1 = default

  hoare step13: extends step1 range 3 post step13=default

  thm step13_valid

  hoare step132: extends step13 range 2 post step132=default

  thm step132_valid

qed

end
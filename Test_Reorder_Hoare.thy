theory Test_Reorder_Hoare
  imports Reorder_Hoare
begin

Hoare program (reorder_hoare) prog: \<open>PROG[x:=1; y:=1; z:=1]\<close>

Hoare invariant (reorder_hoare) start: "\<lambda>m. True"

Hoare step1: range 1 pre start post step1 = default

Hoare' invariant_has step1x: step1 \<rightarrow> "\<lambda>m. m STR ''x'' = 1"
  apply updated by auto

Hoare step13: extends step1 range 3 post step13=default

Hoare' invariant_has step13x: step13 \<rightarrow> "\<lambda>m. m STR ''x'' = 1"
  using step1x
  apply untouched by auto

Hoare' invariant_has step13z: step13 \<rightarrow> "\<lambda>m. m STR ''z'' = 1"
  apply updated by auto

Hoare step132: extends step13 range 2 post step132=default

Hoare' invariant_has step132x: step132 \<rightarrow> "\<lambda>m. m STR ''x'' = 1"
  using step13x
  apply untouched by auto

Hoare' invariant_has step132z: step132 \<rightarrow> "\<lambda>m. m STR ''z'' = 1"
  using step13z
  apply untouched by auto

Hoare' invariant_has step132y: step132 \<rightarrow> "\<lambda>m. m STR ''y'' = 1"
  apply updated by auto

end

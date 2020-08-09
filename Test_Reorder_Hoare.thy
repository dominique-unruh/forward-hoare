theory Test_Reorder_Hoare
  imports Reorder_Hoare
begin

lemma True proof

hoare program (reorder_hoare) prog1: \<open>PROG[x:=1; y:=1; z:=1]\<close>

hoare invariant (reorder_hoare) start: "\<lambda>m. True"

hoare step1: range 1 pre start post step1 = default

hoare' invariant_has step1x: step1 \<rightarrow> "\<lambda>m. m STR ''x'' = 1"
  apply updated by auto

hoare step13: extends step1 range 3 post step13=default

from \<open>{step1 \<Rightarrow> \<lambda>m. m STR ''x'' = 1}\<close>
hoare' invariant_has step13x: step13 \<rightarrow> "\<lambda>m. m STR ''x'' = 1"
  using step1x
  apply untouched by auto

hoare' invariant_has step13z: step13 \<rightarrow> "\<lambda>m. m STR ''z'' = 1"
  apply updated by auto

hoare step132: extends step13 range 2 post step132=default

hoare' invariant_has step132x: step132 \<rightarrow> "\<lambda>m. m STR ''x'' = 1"
  using step13x
  apply untouched by auto

hoare' invariant_has step132z: step132 \<rightarrow> "\<lambda>m. m STR ''z'' = 1"
  using step13z
  apply untouched by auto

hoare' invariant_has step132y: step132 \<rightarrow> "\<lambda>m. m STR ''y'' = 1"
  apply updated by auto

qed

end

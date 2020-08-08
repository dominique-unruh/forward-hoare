theory Test_Tmp_Hoare
  imports Tmp_Hoare
begin

record memory = mem_x :: int   mem_y :: "int \<Rightarrow> nat"   mem_z :: nat

definition "x_raw (m::memory) = (mem_x m, m\<lparr>mem_x := 0\<rparr>)"
lemma valid_x_raw: "valid_var (x_raw, UNIV)"
  unfolding valid_var_def x_raw_def case_prod_conv
  apply (rule exI[of _ "{m\<lparr>mem_x := 0\<rparr> | m. True}"])
  apply (rule bij_betw_byWitness[where f'="\<lambda>(v,m). m\<lparr>mem_x := v\<rparr>"])
  by auto

lift_definition x :: "(memory,int) var" is x_raw
  by (rule valid_x_raw)

lemma [simp]: "has_variables TYPE(memory) TYPE(int)"
  using valid_x_raw by auto  

lemma [simp]: "eval_var x m = mem_x m"
  apply transfer using valid_x_raw unfolding x_raw_def by auto

lemma [simp]: "inj x_raw"
  using valid_x_raw
  by (metis (no_types, lifting) Pair_inject iffs injI surjective update_convs(1) x_raw_def)

lemma [simp]: "update_var x a m = m\<lparr>mem_x := a\<rparr>"
  apply transfer apply (simp add: valid_x_raw)
  apply (rule inv_f_eq)
   apply simp
  unfolding x_raw_def by simp








definition "y_raw (m::memory) = (mem_y m, m\<lparr>mem_y := undefined\<rparr>)"
lemma valid_y_raw: "valid_var (y_raw, UNIV)"
  unfolding valid_var_def y_raw_def case_prod_conv
  apply (rule exI[of _ "{m\<lparr>mem_y := undefined\<rparr> | m. True}"])
  apply (rule bij_betw_byWitness[where f'="\<lambda>(v,m). m\<lparr>mem_y := v\<rparr>"])
  by auto

lift_definition y :: "(memory,int\<Rightarrow>nat) var" is y_raw
  by (rule valid_y_raw)

lemma [simp]: "has_variables TYPE(memory) TYPE(int\<Rightarrow>nat)"
  using valid_y_raw by auto  

lemma [simp]: "eval_var y m = mem_y m"
  apply transfer using valid_y_raw unfolding y_raw_def by auto

lemma [simp]: "inj y_raw"
  using valid_y_raw
  by (metis (no_types, lifting) Pair_inject iffs injI surjective update_convs(2) y_raw_def)

lemma [simp]: "update_var y a m = m\<lparr>mem_y := a\<rparr>"
  apply transfer apply (simp add: valid_y_raw)
  apply (rule inv_f_eq)
   apply simp
  unfolding y_raw_def by simp




definition "z_raw (m::memory) = (mem_z m, m\<lparr>mem_z := 0\<rparr>)"
lemma valid_z_raw: "valid_var (z_raw, UNIV)"
  unfolding valid_var_def z_raw_def case_prod_conv
  apply (rule exI[of _ "{m\<lparr>mem_z := 0\<rparr> | m. True}"])
  apply (rule bij_betw_byWitness[where f'="\<lambda>(v,m). m\<lparr>mem_z := v\<rparr>"])
  by auto

lift_definition z :: "(memory,nat) var" is z_raw
  by (rule valid_z_raw)

lemma [simp]: "has_variables TYPE(memory) TYPE(nat)"
  using valid_z_raw by auto  

lemma [simp]: "eval_var z m = mem_z m"
  apply transfer using valid_z_raw unfolding z_raw_def by auto

lemma [simp]: "inj z_raw"
  using valid_z_raw unfolding valid_var_def case_prod_conv
  using bij_betw_imp_inj_on by blast 

lemma [simp]: "update_var z a m = m\<lparr>mem_z := a\<rparr>"
  apply transfer apply (simp add: valid_z_raw)
  apply (rule inv_f_eq)
   apply simp
  unfolding z_raw_def by simp


lemma [simp, independence]:
  "independent_vars x y" "independent_vars y x"
  "independent_vars x z" "independent_vars z x"
  "independent_vars y z" "independent_vars z y"
  unfolding independent_vars_def by simp_all

lemma [simp]:
  "independent_of mem_x y" "independent_of mem_y x"
  "independent_of mem_x z" "independent_of mem_z x"
  "independent_of mem_y z" "independent_of mem_z y"
  unfolding independent_of_def by simp_all

Hoare config (tmp_hoare) memory = memory

Hoare program (tmp_hoare) left: \<open>PROG[x:=1; y:=nat; z:=$y ($x)]\<close>
Hoare program (tmp_hoare) right: \<open>PROG[x:=2; y:=nat; z:=$y ($x) + 1]\<close>

ML \<open>
Forward_Hoare.Hoare_Data.get (Context.Proof \<^context>) |> #programs
\<close>

Hoare config (tmp_hoare) left = left
Hoare config (tmp_hoare) right = right

Hoare invariant (tmp_hoare) start2: "INV2[True] :: (memory, memory) rinvariant"

Hoare step1: range 1~1 pre start2 post step1 = default

Hoare' invariant_has step1x1: step1 \<rightarrow> "INV2[$x1=1] :: (memory,memory) rinvariant"
  apply updated by auto

Hoare' invariant_has step1x2: step1 \<rightarrow> "INV2[$x2=2] :: (memory,memory) rinvariant"
  apply updated by auto

Hoare' invariant_has step1x: step1 \<rightarrow> "INV2[$x1+1=$x2]"
  using step1x1 step1x2 by auto

Hoare step2: range 2~2 pre step1 post step2 = default

Hoare' invariant_has step2x1: step2 \<rightarrow> "INV2[$x1=1] :: (memory,memory) rinvariant"
  using step1x1 apply untouched by auto

lemma True
proof -

  hoare invariant (tmp_hoare) start: "\<lambda>m. True"

  hoare step1: range 1 pre start post step1 = default

  hoare' invariant_has step1x: step1 \<rightarrow> "INV[$x = 1]"
    apply updated by auto

  hoare step13: extends step1 range 3 post step13=default

  from step1x
  hoare' invariant_has step13x: step13 \<rightarrow> "INV[$x = 1]"
    apply untouched by auto

  hoare' invariant_has step13z: step13 \<rightarrow> "INV[$z = 7]"
    apply updated by auto

  hoare step132: extends step13 range 2 post step132=default

  from step13x
  hoare' invariant_has step132x: step132 \<rightarrow> "INV[$x = 1]"
    apply untouched by auto

  from step13z
  hoare' invariant_has step132z: step132 \<rightarrow> "INV[$z=7]"
    apply untouched by auto

  hoare' invariant_has step132y: step132 \<rightarrow> "INV[$y=nat]"
    apply updated by auto

qed

end

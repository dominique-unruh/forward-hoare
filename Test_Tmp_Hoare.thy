theory Test_Tmp_Hoare
  imports Tmp_Hoare
begin

record memory = mem_x :: int   mem_y :: "real"   mem_z :: nat

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

lift_definition y :: "(memory,real) var" is y_raw
  by (rule valid_y_raw)

lemma [simp]: "has_variables TYPE(memory) TYPE(real)"
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

Hoare program (tmp_hoare) left:  \<open>PROG[x:=$x+1; z:=nat ($x); y <$ spmf_of_set {1,2}]\<close>
Hoare program (tmp_hoare) right: \<open>PROG[x:=$x+2; z:=nat ($x); y <$ spmf_of_set {2,3}]\<close>

Hoare config (tmp_hoare) left = left
Hoare config (tmp_hoare) right = right

lemma True proof

  hoare invariant (tmp_hoare) 
    start2: "INV2[$x1=$x2+1 \<and> $z1=$z2] :: (memory, memory) rinvariant"

  have [hoare_invi]: "{start2 \<Rightarrow> $z1=$z2}"
    unfolding start2_inv_def by simp

  (* TODO should work *)
  (* thm \<open>{start2 \<Rightarrow> $x1=$x2}\<close> *)

  hoare' step1L: range 1 ~ \<emptyset> pre start2 post step1L = default
    (* TODO: should be automatic *)
    by auto

  have [hoare_invi]: "{step1L \<Rightarrow> $x1=$x2+2}"
    apply wp
    using start2_inv_def by auto

  hoare' step1LR: range \<emptyset> ~ 1 pre step1L post step1LR = default
    (* TODO: should be automatic *)
    by auto

(* TODO: pretty_range should include the \<emptyset> *)

  have bla [hoare_invi]: "{step1LR \<Rightarrow> $x1=$x2}"
    apply wp
    using \<open>{step1L \<Rightarrow> $x1=$x2+2}\<close> 
    by auto

  hoare' step2: range 2~2 pre step1LR post step2 = default
    (* TODO: should be automatic *)
    by auto

   (* hoare preserve bla: \<open>{step1LR \<Rightarrow> $x1=$x2}\<close> in step2  *)

(*   have [hoare_invi]: "{step2 \<Rightarrow> $x1=$x2}"
    using \<open>{step1LR \<Rightarrow> $x1=$x2}\<close> by untouched *)

  have [hoare_invi]: "{step2 \<Rightarrow> $z1=$z2}"
    apply wp
    using \<open>{step1LR \<Rightarrow> $x1=$x2}\<close>
    by simp

  hoare' step3: range 3~3 pre step2 post step3 = 
        rnd \<open>\<lambda>m1 m2. map_spmf (\<lambda>x. (x,x+1)) (spmf_of_set {1,2})\<close>
    by auto

  have \<open>{step3 \<Rightarrow> $y1+1=$y2}\<close>
    apply wp by simp

  from \<open>{step3 \<Rightarrow> $x1=$x2}\<close> \<open>{step3 \<Rightarrow> $z1=$z2}\<close>
  have [hoare_invi]: "{step3 \<Rightarrow> $x1*$z1 = $x2*$z2}"
    by auto

qed

end

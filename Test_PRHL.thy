theory Test_PRHL
  imports PRHL
begin

record memory = mem_x :: int   mem_y :: "real"   mem_z :: nat


definition "x_raw = (mem_x, \<lambda>a m. m\<lparr>mem_x := a\<rparr>)"

lemma valid_x_raw: "valid_raw_var (UNIV, x_raw)"
  unfolding x_raw_def apply (rule valid_raw_varI) by auto

lift_definition x :: "(memory,int) var" is x_raw
  using valid_x_raw by auto

lemma [simp]: "valid_var x"
  apply transfer using valid_x_raw by auto  

lemma [simp]: "eval_var x m = mem_x m"
  apply transfer using valid_x_raw unfolding x_raw_def by auto

lemma [simp]: "update_var x a m = m\<lparr>mem_x := a\<rparr>"
  apply transfer unfolding x_raw_def by simp


definition "y_raw = (mem_y, \<lambda>a m. m\<lparr>mem_y := a\<rparr>)"

lemma valid_y_raw: "valid_raw_var (UNIV, y_raw)"
  unfolding y_raw_def apply (rule valid_raw_varI) by auto

lift_definition y :: "(memory,real) var" is y_raw
  using valid_y_raw by auto

lemma [simp]: "valid_var y"
  apply transfer using valid_y_raw by auto  

lemma [simp]: "eval_var y m = mem_y m"
  apply transfer using valid_y_raw unfolding y_raw_def by auto

lemma [simp]: "update_var y a m = m\<lparr>mem_y := a\<rparr>"
  apply transfer unfolding y_raw_def by simp


definition "z_raw = (mem_z, \<lambda>a m. m\<lparr>mem_z := a\<rparr>)"

lemma valid_z_raw: "valid_raw_var (UNIV, z_raw)"
  unfolding z_raw_def apply (rule valid_raw_varI) by auto

lift_definition z :: "(memory,nat) var" is z_raw
  using valid_z_raw by auto

lemma [simp]: "valid_var z"
  apply transfer using valid_z_raw by auto  

lemma [simp]: "eval_var z m = mem_z m"
  apply transfer using valid_z_raw unfolding z_raw_def by auto

lemma [simp]: "update_var z a m = m\<lparr>mem_z := a\<rparr>"
  apply transfer unfolding z_raw_def by simp





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


Hoare config (prhl) memory = memory

Hoare program (prhl) left:  \<open>PROG[x:=$x+1; z:=nat ($x); y <$ spmf_of_set {1,2}]\<close>
Hoare program (prhl) right: \<open>PROG[x:=$x+2; z:=nat ($x); y <$ spmf_of_set {2+$z,3+$z}]\<close>

Hoare config (prhl) left = left
Hoare config (prhl) right = right

lemma True proof

  hoare invariant (prhl) 
    start2: "INV2[$x1=$x2+1 \<and> $z1=$z2] :: (memory, memory) rinvariant"

  thm \<open>{start2 \<Rightarrow> $x1=$x2+1}\<close>
  thm \<open>{start2 \<Rightarrow> $z1=$z2}\<close>
  
  hoare step1L: range 1 ~ \<emptyset> pre start2 post step1L = default

  have [hoare_invi]: "{step1L \<Rightarrow> $x1=$x2+2}"
    apply wp
    using start2_inv_def by auto

  hoare step1LR: extends step1L range \<emptyset> ~ 1 post step1LR = default

  have bla [hoare_invi]: "{step1LR \<Rightarrow> $x1=$x2}"
    apply wp
    using \<open>{step1L \<Rightarrow> $x1=$x2+2}\<close>
    by auto

  hoare step2: extends step1LR range 2~2 post step2 = default

  have [hoare_invi]: "{step2 \<Rightarrow> $z1=$z2}"
    apply wp
    using \<open>{step1LR \<Rightarrow> $x1=$x2}\<close>
    by simp

  hoare' step3test: extends step2 range 3~3 post step3test = default
    by auto

  hoare' step3: extends step2 range 3~3 post step3 = 
        rnd \<open>EXPR2[map_spmf (\<lambda>x. (x,x+1+$z2)) (spmf_of_set {1,2})]\<close>
    by auto

  have \<open>{step3 \<Rightarrow> $y1+1+$z2=$y2}\<close>
    apply wp by simp

  from \<open>{step3 \<Rightarrow> $x1=$x2}\<close> \<open>{step3 \<Rightarrow> $z1=$z2}\<close>
  have [hoare_invi]: "{step3 \<Rightarrow> $x1*$z1 = $x2*$z2}"
    by auto

qed

end

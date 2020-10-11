theory Test_PRHL
  imports PRHL
begin

record memory = mem_x :: nat   mem_y :: nat  mem_z :: nat

declare_variables
  x get "mem_x" set "\<lambda>a m. m\<lparr>mem_x := a\<rparr>" and
  y get "mem_y" set "\<lambda>a m. m\<lparr>mem_y := a\<rparr>" and
  z get "mem_z" set "\<lambda>a m. m\<lparr>mem_z := a\<rparr>"
  by auto

Hoare config (prhl) memory = memory

Hoare program (prhl) right: \<open>PROG[y:=$y+1; if $y < $x then y := $y+$x else {}]\<close>
Hoare program (prhl) left:  \<open>PROG[z:=$z+1; if $x < $y then x := $x+$y else {}]\<close>

Hoare config (prhl) left = left
Hoare config (prhl) right = right

lemma True proof

  (* TODO should not be needed *)
  have [independence]: "independent_of (\<lambda>mem. eval_var x mem < eval_var y mem) z"
    by (tactic \<open>PRHL.independence_tac \<^context> 1\<close>)
  have [independence]: "independent_of (\<lambda>mem. eval_var x mem + eval_var y mem) z"
    by (tactic \<open>PRHL.independence_tac \<^context> 1\<close>)
  have [independence]: "independent_of (\<lambda>mem. eval_var z mem + 1) x"
    by (tactic \<open>PRHL.independence_tac \<^context> 1\<close>)


  hoare invariant (prhl) startTest: \<open>INV[True]\<close>
  hoare ifstart: range 1 pre startTest post ifstart = default
  
  hoare iftrue: extends ifstart range 2t(0) post test = default
(*   have [hoare_invi]: "{test \<Rightarrow> $x < $y}"
    apply wp by simp *)

  hoare iftruesetx: extends iftrue range 2t(1) post iftruesetx = default
  have [hoare_invi]: \<open>{iftruesetx \<Rightarrow> $x \<ge> $y}\<close>
    apply wp by auto

  hoare iffalse: extends ifstart range 2f(0) post iffalse = default
  have [hoare_invi]: "{iffalse \<Rightarrow> $x \<ge> $y}"
    apply wp by simp


  hoare merge afterif = iftruesetx + iffalse = default

  hoare afterif: range \<emptyset> pre iftruesetx (* also: iffalse *) post afterif = default
(* TODO *)

  have "\<exists>P. program_sums true (Block PROG[assert $x < $y; x := $x + $y] # PROG[])
                              (Block PROG[assert \<not> $x < $y] # PROG[])
                              P"
    apply (rule exI)
    apply (rule spmf_sums_left_distrib1)
    by (rule spmf_sums_If)

  have "\<exists>A c. hoare (A::memory invariant) c INV[$x \<ge> $y]"
    apply (rule exI; rule exI)
    using iftruesetx_valid iffalse_valid apply (rule spmf_sums_hoare')
    apply (rule spmf_sums_right_distrib_UNIV1)
    apply (rule spmf_sums_left_distrib1)
    apply (rule spmf_sums_If)
    using \<open>{iftruesetx \<Rightarrow> $x \<ge> $y}\<close> \<open>{iffalse \<Rightarrow> $x \<ge> $y}\<close> by auto




  hoare invariant (prhl) start': \<open>INV2[$x1=$y2 \<and> $y1=$x2] :: (memory,memory) rinvariant\<close>
  (* TODO: why do we need to enforce the type here? *)


  hoare step1': range 1~1 pre start' post step1' = default
  have step1'_imp[hoare_invi]: \<open>{step1' \<Rightarrow> $x1=$y2 \<and> $y1=$x2}\<close>
    apply wp using start'_inv_def by auto

  hoare step2': extends step1' range 2~2 post step2' = default

  have step2'_imp[hoare_invi]: \<open>{step2' \<Rightarrow> $x1=$y2 \<and> $y1=$x2}\<close>
    apply wp using step1'_imp by auto

  hoare invariant (prhl) start: "INV[$x\<ge>$y \<and> $x\<noteq>0]"
  hoare step1: range 1 pre start post step1 = default

  have [hoare_invi]: \<open>{step1 \<Rightarrow> $x>0}\<close>
    apply wp by simp

  hoare step2: extends step1 range 2 post step2 = default
  have [hoare_invi]: \<open>{step2 \<Rightarrow> $x\<noteq>0}\<close>
    apply wp using \<open>{step1 \<Rightarrow> $x>0}\<close> by simp

  have [hoare_invi]: \<open>{step2 \<Rightarrow> $x\<ge>$y}\<close>
    apply wp using \<open>{step1 \<Rightarrow> $x>0}\<close> by simp
qed

end

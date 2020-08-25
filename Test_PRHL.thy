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
Hoare program (prhl) left:  \<open>PROG[x:=$x+1; if $x < $y then x := $x+$y else {}]\<close>

Hoare config (prhl) left = left
Hoare config (prhl) right = right

lemma True proof

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

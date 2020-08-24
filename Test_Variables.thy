theory Test_Variables
  imports Variables
begin

record memory = mem_x :: int   mem_y :: "int"   mem_z :: nat

declare_variables 
  x get "mem_x :: memory \<Rightarrow> _" set "\<lambda>a m. m\<lparr>mem_x := a\<rparr>" and
  y get "mem_y" set "\<lambda>a m. m\<lparr>mem_y := a\<rparr>" and
  z get "mem_z" set "\<lambda>a m. m\<lparr>mem_z := a\<rparr>"
  by auto

print_theorems

(* Test *)

lemma
  "independent_vars x y" "independent_vars y x"
  "independent_vars x z" "independent_vars z x"
  "independent_vars y z" "independent_vars z y"
  "independent_of mem_x y" "independent_of mem_y x"
  "independent_of mem_x z" "independent_of mem_z x"
  "independent_of mem_y z" "independent_of mem_z y"
  by simp_all

end

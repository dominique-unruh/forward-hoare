theory Test_Variables
  imports Variables
begin

record memory = mem_x :: int   mem_y :: "int"   mem_z :: nat

(* TODO: Should be possible to declare many variables in one go,
    together with independence theorems *)
declare_variable x get "mem_x" set "\<lambda>a m. m\<lparr>mem_x := a\<rparr>"
  by auto

declare_variable y get "mem_y" set "\<lambda>a m. m\<lparr>mem_y := a\<rparr>"
  by auto

declare_variable z get "mem_z" set "\<lambda>a m. m\<lparr>mem_z := a\<rparr>"
  by auto

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

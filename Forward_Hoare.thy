theory Forward_Hoare
  imports Pure
  keywords "do" :: prf_decl % "proof"
    and "do_prf" :: prf_goal % "proof"
    and "program" :: prf_decl % "proof"
    and "invariant" :: prf_decl % "proof"
begin

ML_file "forward_hoare.ML"

end

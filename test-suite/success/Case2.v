(* ============================================== *)
(*     To test compilation of dependent case      *)
(*  Nested patterns                               *)
(* ============================================== *)

Type
  match 0 as n return (n = n) with
  | O => refl_equal 0
  | m => refl_equal m
  end.



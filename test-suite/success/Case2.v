(* ============================================== *)
(*     To test compilation of dependent case      *)
(*  Nested patterns                               *)
(* ============================================== *)

Type <[n:nat]n=n>Cases O of 
                    O => (refl_equal nat O) 
                  | m => (refl_equal nat m) 
end.



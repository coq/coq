(* Test error messages *)

(* Test non-regression of bug fixed in r13486 (bad printer for module names) *)

Module Type S.
Parameter t:Type.
End S.
Module M : S.
Fail End M.

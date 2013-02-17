(* Test error messages *)

(* Test non-regression of bug fixed in r13486 (bad printer for module names) *)

Module Type S.
Parameter t:Type.
End S.
Module M : S.
Fail End M.

(* A simple check of how Ltac trace are used or not *)
(* Unfortunately, cannot test error location... *)

Ltac f x := apply x.
Goal True.
Fail simpl; apply 0.
Fail simpl; f 0.
Abort.

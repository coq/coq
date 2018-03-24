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

(* Test instantiate error messages *)

Goal forall T1 (P1 : T1 -> Type), sigT P1 -> sigT P1.
intros T1 P1 H1.
eexists ?[x].
destruct H1 as [x1 H1].
Fail instantiate (x:=projT1 x1).
Abort.

(* Test some messages for non solvable evars *)

Fail Goal forall a f, f a = 0.
Fail Goal forall f x, id f x = 0.
Fail Goal forall f P,  P (f 0).

(* Cf BZ#546 *)

Require Import Omega.

Section S.

Variables n m : nat.
Variable H : n<m.

Inductive Dummy : nat -> Set :=
| Dummy0 : Dummy 0
| Dummy2 : Dummy 2
| DummyApp : forall i j, Dummy i -> Dummy j -> Dummy (i+j).

Definition Bug : Dummy (2*n).
Proof.
induction n.
 simpl ; apply Dummy0.
 replace (2 * S n0) with (2*n0 + 2) ; auto with arith.
  apply DummyApp.
   2:exact Dummy2.
   apply IHn0 ; abstract omega.
Defined.

End S.


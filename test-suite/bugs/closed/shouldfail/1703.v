(* Check correct binding of intros until used in Ltac *)

Ltac intros_until n := intros until n.

Goal forall i j m n : nat, i = 0 /\ j = 0 /\ m = 0 /\ n = 0.
intro i.
Fail intros until i.
Abort.

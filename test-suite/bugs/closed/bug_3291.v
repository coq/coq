Require Import Setoid.

Definition segv : forall x, (x = 0%nat) -> (forall (y : nat), (y < x)%nat -> nat) = forall (y : nat), (y < 0)%nat -> nat.
intros x eq.
assert (H : forall y, (y < x)%nat = (y < 0)%nat).
rewrite -> eq. auto.
Set Typeclasses Debug.
Fail setoid_rewrite <- H. (* The command has indeed failed with message:
=> Stack overflow. *)

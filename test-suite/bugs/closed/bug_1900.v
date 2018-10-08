Parameter A : Type .

Definition eq_A := @eq A.

Goal forall x, eq_A x x.
intros.
reflexivity.
Qed.

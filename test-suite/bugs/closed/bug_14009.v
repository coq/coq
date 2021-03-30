Class Bin {P:Type} (A B : P) := {}.

Set Primitive Projections.

Record test (n : nat) := { proj : Prop }.
Axiom Bin_test : forall {t1 t2 : test O}, Bin (proj _ t1) (proj _ t2).

Create HintDb db discriminated.
#[local] Hint Resolve Bin_test : db.
#[local] Hint Opaque proj : db.

Goal forall t1 t2 : test O, Bin (proj O t1) (proj O t2).
Proof.
intros.
solve [typeclasses eauto with db].
Qed.

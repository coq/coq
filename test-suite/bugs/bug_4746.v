Variables P Q : nat -> Prop.
Variable f : nat -> nat.

Goal forall (x:nat), (forall y, P y -> forall z, Q z -> y=f z -> False) -> False.
Proof.
intros.
ecase H with (3:=eq_refl).
Abort.

Goal forall (x:nat), (forall y, y=x -> False) -> False.
Proof.
intros.
unshelve ecase H with (1:=eq_refl).
Qed.

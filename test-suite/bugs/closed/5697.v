Set Primitive Projections.

Record foo : Type := Foo { foo_car: nat }.

Goal forall x y : nat, x <> y -> Foo x <> Foo y.
Proof.
intros.
intros H'.
congruence.
Qed.

Record bar (A : Type) : Type := Bar { bar_car: A }.

Goal forall x y : nat, x <> y -> Bar nat x <> Bar nat y.
Proof.
intros.
intros H'.
congruence.
Qed.

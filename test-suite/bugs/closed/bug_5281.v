Inductive A (T : Prop) := B (_ : T).
Scheme Equality for A.

Goal forall (T:Prop), (forall x y : T, {x=y}+{x<>y}) -> forall x y : A T, {x=y}+{x<>y}.
decide equality.
Qed.

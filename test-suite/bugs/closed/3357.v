Notation D1 := (forall {T : Type} ( x : T ) , Type).

Definition DD1 ( A : forall {T : Type} (x : T), Type ) := A 1.
Definition DD1' ( A : D1 ) := A 1.


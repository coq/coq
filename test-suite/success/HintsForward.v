
Parameter pred : nat -> Prop.
Parameter pred0 : pred 0.
Parameter f : nat -> nat.
Parameter predf : forall n, pred n -> pred (f n).

Parameter pred2 : nat -> Prop.
Lemma foo n : pred n -> pred (S n).
Admitted.

Hint Extern 0 => match goal with [ H : pred ?n |- _ ] => pose (foo n H) end : bla.

Hint Extern 100000 => shelve : bla.

Goal pred 0 -> True.
  intros.
  unshelve typeclasses eauto 4 with bla.

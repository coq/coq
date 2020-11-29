Inductive foo : Set -> Type := Foo : foo unit.

Lemma bar U (pf : unit = U) : forall (x : foo U), x = eq_rect unit foo Foo U pf.
Proof.
  intros [].
Abort.

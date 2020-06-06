Parameter A B : Prop.
Axiom P : inhabited (A -> B).

Goal A -> True.
Proof.
  Fail intros ?%P ?.
  Fail intros []%P.
  intro a.
  Fail apply P in a as [].
Abort.

Inductive paths {A} (x : A) : A -> Type := idpath : paths x x.
Goal forall A B : Set, @paths Type A B -> @paths Set A B.
Proof.
  intros A B H.
  Fail exact H.
Abort.

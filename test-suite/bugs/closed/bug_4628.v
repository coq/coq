Module first.
  Polymorphic Record BAR (A:Type) :=
  { foo: A->Prop; bar: forall (x y: A), foo x -> foo y}.

Section A.
Context {A:Type}.

Set Printing Universes.

Hint Resolve bar.
Goal forall (P:BAR A) x y, foo _ P x -> foo _ P y.
intros.
eauto.
Qed.
End A.
End first.

Module firstbest.
  Polymorphic Record BAR (A:Type) :=
  { foo: A->Prop; bar: forall (x y: A), foo x -> foo y}.

Section A.
Context {A:Type}.

Set Printing Universes.

Polymorphic Hint Resolve bar.
Goal forall (P:BAR A) x y, foo _ P x -> foo _ P y.
intros.
eauto.
Qed.
End A.
End firstbest.

Module second.
Axiom foo: Set.
Axiom foo': Set.

Polymorphic Record BAR (A:Type) :=
  { bar: foo' -> foo}.
Set Printing Universes.

Lemma baz@{i}: forall (P:BAR@{Set} nat), foo' -> foo.
  eauto using bar.
Qed.
End second.

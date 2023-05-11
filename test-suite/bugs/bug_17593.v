Global Set Universe Polymorphism.
Global Set Polymorphic Inductive Cumulativity.

Record prd A B := pr { p1 : A ; p2 : B }.

Section foo.
  Universes i.
  Context {A:Type@{i}} (R:A -> A -> Prop) (op:prd A A -> A).
  Notation "x > y" := (R x y).
  Notation "x + y" := (op (pr _ _ x y)).
  Context (transitivity: forall x y z, x > y -> y > z -> x > z).

  Lemma foo x y z : x + y + z > y.
  Proof.
    refine (transitivity _ (x + y) _ _ _).
    1: {
    match goal with |- ?a + _ > ?a => idtac a end.
  Abort.
End foo.

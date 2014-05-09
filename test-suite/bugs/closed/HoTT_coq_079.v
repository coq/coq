Set Primitive Projections.
Set Implicit Arguments.
Set Universe Polymorphism.

Inductive paths A (x : A) : A -> Type := idpath : paths x x.

Notation "x = y :> A" := (@paths A x y).
Notation "x = y" := (x = y :> _).

Record foo := { x : Type; H : x = x }.

Create HintDb bar discriminated.
Hint Resolve H : bar.
Goal forall y : foo, @x y = @x y.
intro y.
progress auto with bar. (* failed to progress *)

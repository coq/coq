Set Primitive Projections.

Polymorphic Record pair {A B : Type} : Type :=
  prod { pr1 : A; pr2 : B }.

Notation " ( x ; y ) " := (@prod _ _ x y).
Notation " x .1 " := (pr1 x) (at level 3).
Notation " x .2 " := (pr2 x) (at level 3).

Goal ((0; 1); 2).1.2 = 1.
Proof.
  cbv.
  match goal with
  | |- ?t = ?t => exact (eq_refl t)
  end.
Qed.


Unset Positivity Checking.

Inductive foo : Type -> Type :=
| bar : foo (foo unit)
| baz : foo nat.

Definition toto : forall A : Type, foo A -> {A = foo unit} + {A = nat}.
Proof.
  intros A x. destruct x; intuition.
Defined.

Check (eq_refl : toto _ baz = right eq_refl).

Require Import ssreflect.

Goal forall y x : nat, x = y -> x = x.
Proof.
move=> + > ->. match goal with |- forall y, y = y => by [] end.
Qed.

Goal forall y x : nat, le x y -> x = y.
Proof.
move=> > [|].
  by [].
match goal with |- forall a, _ <= a -> _ = S a => admit end.
Admitted.

Goal forall y x : nat, le x y -> x = y.
Proof.
move=> y x.
case E: x => >.
  admit.
match goal with |- S _ <= y -> S _ = y => admit end.
Admitted.

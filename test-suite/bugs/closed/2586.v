Require Import Setoid SetoidClass Program.

Goal forall `(Setoid nat) x y, x == y -> S x == S y.
  intros.
  Fail clsubst H0.
  Abort.

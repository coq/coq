Require Import Setoid.
Goal forall x y : Set, x = y -> y = y.
intros x y H.
rewrite_strat try topdown terms H.

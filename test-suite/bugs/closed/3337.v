Require Import Setoid.
Goal forall x y : Set, x = y -> x = y.
intros x y H.
rewrite_strat subterms H.


Require Import Setoid.

Fail Goal forall x, impl True (x = 0) -> x = 0 -> False.
(*intros x H E.
rewrite H in E.*)

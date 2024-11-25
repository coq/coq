(* additional test cases for manual testing *)
Goal 1 + 1 = 3 -> False -> True.
intro. clear H; intro.
Abort.

Goal nat -> bool -> nat -> True.
intros i b j.
revert b.
cbn.
Abort.

Require Import Corelib.Init.Number.

Goal int -> uint -> nat -> nat -> nat -> nat ->True.
  intros a b c.
clear a b c; intros b a c.
Abort.

Goal int -> nat -> uint -> nat -> nat -> nat -> True.
  intros a b c.
clear a b c; intros c a b.
Abort.

Goal uint -> int -> nat -> nat -> nat -> nat -> True.
intros a b c. clear a b c; intros b a c.
Abort.

Goal nat -> int -> int -> nat -> nat -> int -> True.
intros a c d. clear a c d; intros a b d.
Abort.

Goal 1 = 0 -> True -> False -> True.
intros X H. clear H; intro.
Abort.

Goal True -> True -> False -> False -> True.
intros H H0. clear H H0; intros H H0.
Abort.

Goal True -> True -> False -> False -> False
  -> True.
intros H H0. clear H H0; intros H H0 H1.
Abort.

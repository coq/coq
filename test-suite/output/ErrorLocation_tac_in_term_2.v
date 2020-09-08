Ltac f x y := apply (x y).

Goal True.
apply ltac:(f S true).
Abort.

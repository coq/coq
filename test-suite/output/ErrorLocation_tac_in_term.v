Ltac f x y := apply (x y).

Goal True.
Fail apply ltac:(apply (S true)).
Fail apply ltac:(f S true).
Abort.

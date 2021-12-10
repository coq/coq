Notation foo := (I I).

Fail Check foo.

Notation bar := (ltac:(exact (I I))) (only parsing).

(* whole command: it would be nice to be more precise *)
Fail Check bar.

Notation baz x := (ltac:(exact x)) (only parsing).

Fail Check baz (I I).

Ltac f x y := apply (x y).

Goal True.
Fail apply ltac:(apply (S true)).
Fail apply ltac:(f S true).
Abort.

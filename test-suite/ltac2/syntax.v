Require Import Ltac2.Ltac2.

Ltac2 Type ('a, 'b, 'c) t.
Ltac2 Type ('a) u.
Ltac2 Type 'a v.

Ltac2 foo
  (f : ('a, 'b, 'c) t -> ('a -> 'a, 'b -> 'c, 'c * 'c) t)
  (x : ('a, 'b, 'c) t) :=
  f x.

Ltac2 bar (x : 'a u) (y : ('b) v) := x.

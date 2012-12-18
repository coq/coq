(* This used to fail in 8.0pl1 *)

Goal forall n, n+n=0->0=n+n.
intros.
set n in * |-.
Abort.

(* This works from 8.4pl1, since merging of different instances of the
   same metavariable in a pattern is done modulo conversion *)

Notation "p .+1" := (S p) (at level 1, left associativity, format "p .+1").

Goal forall (f:forall n, n=0 -> Prop) n (H:(n+n).+1=0), f (n.+1+n) H.
intros.
set (f _ _).
Abort.




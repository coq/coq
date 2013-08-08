(* Simpl with patterns *)

Goal forall x, 0+x = 1+x.
intro x.
simpl (_ + x).
Show.
Undo 2.
simpl (_ + x) at 2.
Show.
Undo 2.
simpl (0 + _).
Show.
Undo 2.

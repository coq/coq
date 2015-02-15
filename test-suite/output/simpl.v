(* Simpl with patterns *)

Goal forall x, 0+x = 1+x.
intro x.
simpl (_ + x).
Show.
Undo.
simpl (_ + x) at 2.
Show.
Undo.
simpl (0 + _).
Show.
Undo.

Class Foo.
Class Bar := b : Type.

Instance foo : Foo := _.
(* 1 subgoals, subgoal 1 (ID 4)
  
  ============================
   Foo *)

Instance bar : Bar.
exact Type.
Defined.
(* bar is defined *)

About foo.
(* foo not a defined object. *)

Fail Defined.

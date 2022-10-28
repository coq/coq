
Class Foo (n:nat) := {}.

Axiom thing : forall n {_:Foo n}, nat.

(* both missing args are reported *)
Fail Goal thing 1 = thing 2.

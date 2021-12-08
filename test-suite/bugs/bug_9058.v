Class A (X : Type) := {}.
Hint Mode A ! : typeclass_instances.

Class B X {aX: A X} Y := { opB: X -> Y -> Y }.
Hint Mode B - - ! : typeclass_instances.

Section Section.

Context X {aX: A X} Y {bY: B X Y}.

(* Set Typeclasses Debug. *)

Let ok := fun (x : X) (y : Y) => opB x y.
Let ok' := fun x (y : Y) => opB x y.

End Section.

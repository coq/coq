
Class C (n:nat) := c{}.

Instance c0 : C 0 := {}.

Definition x := 0.

Opaque x.

Type _ : C x.
(* this is maybe wrong behaviour, if it changes just update the test *)

Hint Opaque x : typeclass_instances.
Transparent x.

Fail Type _ : C x.

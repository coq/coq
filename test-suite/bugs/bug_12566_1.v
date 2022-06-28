
Class C (n:nat) := c{}.

#[export] Instance c0 : C 0 := {}.

Definition x := 0.

Opaque x.

Type _ : C x.
(* this is maybe wrong behaviour, if it changes just update the test *)

#[export] Hint Opaque x : typeclass_instances.
Transparent x.

Fail Type _ : C x.

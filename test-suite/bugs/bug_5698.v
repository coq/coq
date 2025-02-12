(* Check that simpl grants the never flag for primitive projections
   independently of the internal folded status *)

Set Primitive Projections.

Record foo := Foo {
  foo_car : Type;
  foo_0 : foo_car;
}.

Arguments foo_car : simpl never.
Arguments foo_0 : simpl never.

Definition nat_foo := Foo nat 0.

Set Printing All.

Goal foo_0 nat_foo = 0.
Proof.
  Fail progress simpl.
  progress unfold foo_0.
  Fail progress simpl.
Abort.

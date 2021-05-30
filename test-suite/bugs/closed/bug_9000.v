Set Primitive Projections.
Class type (t : Type) : Type :=
  { bar : t -> Prop  }.

Instance type_nat : type nat :=
  { bar := fun _ => True }.

Definition foo_bar {n : nat} : bar n := I.

#[local] Hint Resolve (@foo_bar) : typeclass_instances.
#[local] Hint Resolve I : typeclass_instances.
Check ltac:(typeclasses eauto with nocore typeclass_instances) : True.
Check ltac:(typeclasses eauto with nocore typeclass_instances foo) : bar _.
Existing Class bar.
Check ltac:(typeclasses eauto with nocore typeclass_instances foo) : bar _.
#[local] Hint Resolve (@foo_bar) : foo.
Check ltac:(typeclasses eauto with nocore typeclass_instances foo) : bar _.

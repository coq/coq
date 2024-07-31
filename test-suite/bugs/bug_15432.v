#[local] Set Typeclasses Strict Resolution.
Class C (P : Prop) (out : Prop) := { c : out -> P}.
#[refine] Instance : C True False := { c := _ }. abstract auto. Defined.
Goal exists q, C True q.
  eexists.
  Fail apply _.
  Fail typeclasses eauto.
  Fail typeclasses eauto with typeclass_instances.
Abort.

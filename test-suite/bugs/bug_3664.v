Require Import TestSuite.admit.
Module NonPrim.
  Unset Primitive Projections.
  Record c := { d : Set }.
  Definition a x := d x.
  Goal forall x, a x.
    intro x.
    Fail progress simpl. (* [progress simpl] fails correctly *)
    Fail progress cbn. (* [progress cbn] fails correctly *)
    admit.
  Defined.
End NonPrim.

Module Prim.
  Set Primitive Projections.
  Record c := { d : Set }.
  Definition a x := d x.
  Goal forall x, a x.
    intro x.
    Fail progress simpl. (* [progress simpl] fails correctly *)
    Fail progress cbn. (* [cbn] succeeds incorrectly, giving [d x] *)
    admit.
  Defined.
End Prim.

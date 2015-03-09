Require Import TestSuite.admit.
Require Import Relation_Definitions RelationClasses Setoid SetoidClass.

Section Bug.

  Context {A : Type} (R : relation A).
  Hypothesis pre : PreOrder R.
  Context `{SA : Setoid A}.

  Goal True.
  set (SA' := SA).
    assert ( forall SA0 : Setoid A,
               @PartialOrder A (@equiv A SA0) (@setoid_equiv A SA0) R pre ).
    rename SA into SA0.
    intro SA.
    admit.
    admit.
Qed.
End Bug.


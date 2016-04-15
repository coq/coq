Set Implicit Arguments.

Generalizable All Variables.

Parameter SpecializedCategory : Type -> Type.
Parameter Object : forall obj, SpecializedCategory obj -> Type.

Section SpecializedFunctor.
  (* Variable objC : Type. *)
  Context `(C : SpecializedCategory objC).

  Record SpecializedFunctor := {
    ObjectOf' : objC -> Type;
    ObjectC : Object C
  }.
End SpecializedFunctor.

Section FunctorInterface.
  Variable objC : Type.
  Variable C : SpecializedCategory objC.
  Variable F : SpecializedFunctor C.

  Set Printing All.
  Set Printing Universes.
  Check @ObjectOf' objC C F. (* Toplevel input, characters 24-25:
Error:
In environment
objC : Type (* Top.515 *)
C : SpecializedCategory objC
F : @SpecializedFunctor (* Top.516 *) objC C
The term "F" has type "@SpecializedFunctor (* Top.516 *) objC C"
 while it is expected to have type
 "@SpecializedFunctor (* Top.519 Top.520 *) objC C". *)

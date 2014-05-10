Set Implicit Arguments.
Set Universe Polymorphism.

Record category :=
  { ob : Type }.

Fail Existing Class category. (*
Toplevel input, characters 0-24:
Anomaly: Mismatched instance and context when building universe substitution.
Please report. *)

Record category' :=
  { ob' : Type;
    hom' : ob' -> ob' -> Type }.

Fail Existing Class category'. (*
Toplevel input, characters 0-24:
Anomaly: Mismatched instance and context when building universe substitution.
Please report. *)

Module Short.
  Set Universe Polymorphism.
  Inductive relevant (A : Type) (B : Type) : Prop := .
  Section foo.
    Variables A B : Type.
    Definition foo := prod (relevant A B) A.
  End foo.

  Section bar.
    Variable A : Type.
    Variable B : Type.
    Definition bar := prod (relevant A B) A.
  End bar.

  Set Printing Universes.
  Check bar nat Set : Set. (* success *)
  Check foo nat Set : Set. (* Toplevel input, characters 6-17:
Error:
The term "foo (* Top.303 Top.304 *) nat Set" has type
"Type (* Top.304 *)" while it is expected to have type
"Set" (Universe inconsistency: Cannot enforce Top.304 = Set because Set
< Top.304)). *)
End Short.

Generalizable All Variables.

Check `(a = 0).
Check `(a = 0)%type.
Definition relation A := A -> A -> Prop.
Definition equivalence `(R : relation A) := True.
Check (`(@equivalence A R)).

Definition a_eq_b : `( a = 0 /\ a = b /\ b > c \/ d = e /\ d = 1).
Admitted.
Print a_eq_b.


Require Import Morphisms.

Class Equiv A := equiv : A -> A -> Prop.
Class Setoid A `{Equiv A} := setoid_equiv :: Equivalence (equiv).

Lemma vcons_proper A `[Equiv A] `[!Setoid A] (x : True) : True.
Admitted.

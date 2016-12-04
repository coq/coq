Set Printing All.
Axiom relation : forall (T : Type), Set.
Axiom T : forall A (R : relation A), Set.
Set Printing Universes.
Parameter (A:_) (R:_) (e:@T A R).

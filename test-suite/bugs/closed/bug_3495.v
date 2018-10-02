Require Import RelationClasses.

Axiom R : Prop -> Prop -> Prop.
Declare Instance : Reflexive R.

Class bar := { x : False }.
Record foo := { a : Prop ; b : bar }.

Definition default_foo (a0 : Prop) `{b : bar} : foo := {| a := a0 ; b := b |}.

Goal exists k, R k True.
Proof.
eexists.
evar (b : bar).
let e := match goal with |- R ?e _ => constr:(e) end in
unify e (a (default_foo True)).
subst b.
reflexivity.

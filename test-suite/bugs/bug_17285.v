
Global Unset Universe Minimization ToSet.

Class Decision (P : Prop) := decide : {P} + {~P}.

Class RelDecision {A B} (R : A -> B -> Prop) :=
  decide_rel x y : Decision (R x y).

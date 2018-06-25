From Coq Require Import ssreflect Setoid.

Structure SEProp := {prop_of : Prop; _ : prop_of <-> True}.

Fact anomaly: forall P : SEProp, prop_of P.
Proof.
move=> [P E].
Fail rewrite E.
Abort.

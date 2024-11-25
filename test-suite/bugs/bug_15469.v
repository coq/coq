Require Import Corelib.ssr.ssreflect.

Class Dist := dist0 : Prop.

Definition dist {Dist : Dist} : Prop := Dist.

Axiom later_dist : Dist.
Axiom foo : later_dist.

Goal @dist later_dist.
Proof.
rewrite /dist.
match goal with [ |- later_dist ] => refine (foo) end.
Qed.

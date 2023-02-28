Require Import Setoid.

Set Printing Existential Instances.

Axiom A : Type.
Axiom i : A.
Axiom Equal : A -> A -> Prop.
Axiom P : A -> Prop.

Axiom everything_equal : forall (j : A), Equal i j.

Instance b : Morphisms.Proper (Equal ==> Basics.impl) P. Admitted.

Axiom forget : P i -> A.

Lemma blah (H : P i) : True.
unshelve rewrite everything_equal in H.
Fail exact (forget H).
Abort.

Lemma blah (H : P i) : True.
unshelve setoid_rewrite everything_equal in H.
Fail exact (forget H).
Abort.

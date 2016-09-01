Require Import Setoid.
Axiom P : nat -> Prop.
Axiom P_or : forall x y, P (x + y) <-> P x \/ P y.
Lemma foo (H : P 3) : False.
eapply or_introl in H.
erewrite <- P_or in H.
(* Error: No such hypothesis: H *)

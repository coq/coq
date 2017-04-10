Require Import Setoid Coq.Classes.Morphisms.
Set Typeclasses Legacy Resolution.

Declare Instance and_Proper_eq: Proper (Logic.eq ==> Logic.eq ==> Logic.eq) and.

Axiom In : Prop.
Axiom union_spec : In <-> True.

Lemma foo : In /\ True.
Proof.
progress rewrite union_spec.
repeat constructor.
Qed.

Require Import Setoid Morphisms Basics.
Lemma foo A B (P : B -> Prop) :
  pointwise_relation _ impl (fun z => A -> P z) P.
Proof.
  Fail reflexivity.

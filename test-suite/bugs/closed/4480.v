Require Import Setoid.

Definition proj (P Q : Prop) := P.

Lemma foo (P : Prop) : proj P P = P.
Admitted.
Lemma trueI : True <-> True.
Admitted.
Goal True.
  Fail setoid_rewrite foo.
  Fail setoid_rewrite trueI.
  

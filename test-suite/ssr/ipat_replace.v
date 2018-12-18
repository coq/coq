Require Import ssreflect.

Lemma test : True.
Proof.
have H : True.
  by [].
have {}H : True.
  by apply: H.
by apply: H.
Qed.

Lemma test2 (H : True) : False -> False.
Proof.
Fail move=> {}W.
move=> {}H.
by apply: H.
Qed.

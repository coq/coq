Require Import ssreflect.

Lemma one : True -> True.
Proof.
move=> () H; exact H.
Qed.

Lemma two : True \/ True -> True.
Proof.
Fail case => ().
Abort.

Lemma three (x : nat) : True.
Proof.
by elim E: x => (|m IH).
Qed.

Require Import ssreflect ssrbool.

Lemma foo b1 : (if b1 then true else false) = b1.
Proof.
  rewrite [if _ then _ else _]andbT.
  reflexivity.
Qed.

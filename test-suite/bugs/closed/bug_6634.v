From Coq Require Import ssreflect.

Lemma normalizeP (p : tt = tt) : p = p.
Proof.
Fail move: {2} tt p.
Abort.

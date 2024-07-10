Theorem foo (b:bool) : b = true \/ b = false.
Proof.
  Fail dependent destruction b.
  Fail dependent induction b.
Abort.

From Stdlib Require Import Equality.

Theorem foo_with_destruction (b:bool) : b = true \/ b = false.
Proof.
  dependent destruction b; auto.
Qed.

Theorem foo_with_induction (b:bool) : b = true \/ b = false.
Proof.
  dependent induction b; auto.
Qed.

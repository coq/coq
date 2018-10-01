Lemma foo : True.
Proof.
Check 0 : nat.
Check 0 : nat.
exact I.
Qed.

Lemma bar : True.
Proof.
pose (0 : nat).
exact I.
Qed.

Require Import Coq.Strings.Ascii.
Open Scope char_scope.

Lemma baz : True.
Proof.
pose "s".
exact I.
Qed.

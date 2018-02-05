Require Import ssreflect.

Module A.

Definition truth := I.

Ltac t :=
  move: truth.

Ltac t' :=
  generalize truth.

End A.

Goal True.
  A.t.
  apply.
Qed.
Require Import PrimInt63 PrimFloat PrimArray ssreflect.

Open Scope uint63_scope.

Lemma test : 2 = PrimInt63.add 1 1.
Proof.
  set X := 2.
  rewrite -[X]/(PrimInt63.add 1 1).
  by [].
Qed.

Open Scope float_scope.

Lemma test2 : 2 = 1 + 1.
Proof.
  set X := 2.
  rewrite -[X]/(1 + 1).
  by [].
Qed.

Lemma test3 : [| | 2 |] = [| | 1 + 1 |].
Proof.
  set X := [| | 2 |].
  rewrite -[X]/([| | 1 + 1 |]).
  by [].
Qed.

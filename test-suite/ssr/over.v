Require Import ssreflect.

Axiom daemon : False. Ltac myadmit := case: daemon.

(** Testing over for the 1-var case *)

Lemma test_over_1_1 : False.
intros.
evar (I : Type); evar (R : Type); evar (x2 : I -> R).
assert (H : forall i : nat, i + 2 * i - i = x2 i).
  intros i.
  unfold x2 in *; clear x2;
  unfold R in *; clear R;
  unfold I in *; clear I.
  apply Under_from_eq.
  Fail done.

  over.
  myadmit.
Qed.

Lemma test_over_1_2 : False.
intros.
evar (I : Type); evar (R : Type); evar (x2 : I -> R).
assert (H : forall i : nat, i + 2 * i - i = x2 i).
  intros i.
  unfold x2 in *; clear x2;
  unfold R in *; clear R;
  unfold I in *; clear I.
  apply Under_from_eq.
  Fail done.

  by rewrite over.
  myadmit.
Qed.

(** Testing over for the 2-var case *)

Lemma test_over_2_1 : False.
intros.
evar (I : Type); evar (J : Type); evar (R : Type); evar (x2 : I -> J -> R).
assert (H : forall i j, i + 2 * j - i = x2 i j).
  intros i j.
  unfold x2 in *; clear x2;
  unfold R in *; clear R;
  unfold J in *; clear J;
  unfold I in *; clear I.
  apply Under_from_eq.
  Fail done.

  over.
  myadmit.
Qed.

Lemma test_over_2_2 : False.
intros.
evar (I : Type); evar (J : Type); evar (R : Type); evar (x2 : I -> J -> R).
assert (H : forall i j : nat, i + 2 * j - i = x2 i j).
  intros i j.
  unfold x2 in *; clear x2;
  unfold R in *; clear R;
  unfold J in *; clear J;
  unfold I in *; clear I.
  apply Under_from_eq.
  Fail done.

  rewrite over.
  done.
  myadmit.
Qed.

Require Import ssreflect.

Axiom daemon : False. Ltac myadmit := case: daemon.

(** Testing over for the 1-var case *)

Lemma test_over_1_1 : forall i : nat, False.
intros.
evar (I : Type); evar (R : Type); evar (x2 : I -> R).
assert (H : i + 2 * i - i = x2 i).
  unfold x2 in *; clear x2;
  unfold R in *; clear R;
  unfold I in *; clear I.
  apply Under_from_eq.
  Fail done.

  over.
  myadmit.
Qed.

Lemma test_over_1_2 : forall i : nat, False.
intros.
evar (I : Type); evar (R : Type); evar (x2 : I -> R).
assert (H : i + 2 * i - i = x2 i).
  unfold x2 in *; clear x2;
  unfold R in *; clear R;
  unfold I in *; clear I.
  apply Under_from_eq.
  Fail done.

  by rewrite over.
  myadmit.
Qed.

(** Testing over for the 2-var case *)

Lemma test_over_2_1 : forall i j : nat, False.
intros.
evar (I : Type); evar (J : Type); evar (R : Type); evar (x2 : I -> J -> R).
assert (H : i + 2 * j - i = x2 i j).
  unfold x2 in *; clear x2;
  unfold R in *; clear R;
  unfold J in *; clear J;
  unfold I in *; clear I.
  apply Under_from_eq.
  Fail done.

  Fail over. (* Bug: doesn't work so we have to make a beta-expansion by hand *)
  rewrite -[i + 2 * j - i]/((fun x y => x + 2 * y - x) i j). (* todo: automate? *)
  over.
  myadmit.
Qed.

Lemma test_over_2_2 : forall i j : nat, False.
intros.
evar (I : Type); evar (J : Type); evar (R : Type); evar (x2 : I -> J -> R).
assert (H : i + 2 * j - i = x2 i j).
  unfold x2 in *; clear x2;
  unfold R in *; clear R;
  unfold J in *; clear J;
  unfold I in *; clear I.
  apply Under_from_eq.
  Fail done.

  rewrite over.
  Fail done. (* Bug: doesn't work so we have to make a beta-expansion by hand *)
  rewrite -[i + 2 * j - i]/((fun x y => x + 2 * y - x) i j). (* todo: automate? *)
  done.
  myadmit.
Qed.

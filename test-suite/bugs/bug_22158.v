From Corelib Require Import ssreflect.

#[universes(polymorphic)]
Definition bar@{i} {A : Type@{i}} (a : A) := 0.
Lemma test_app (x : nat) : bar x = bar x.
Proof.
  move/bar: x. reflexivity.
Qed.

Lemma test_app2 (x : nat) : x = x.
Proof.
  (* Works for arbitrary flexibles *)
  assert (bar x = bar x).
  move/bar: x. reflexivity.
  reflexivity.
Qed.

#[universes(polymorphic)]
Lemma test_app_imposs@{i j | i < j} (x : nat) : bar@{i} x = bar@{j} x.
Proof.
  move/bar: x. reflexivity.
Qed.

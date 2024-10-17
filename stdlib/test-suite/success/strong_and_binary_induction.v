(** This file is meant to test that the induction lemmas introduced in
    #18628:
    - [binary_induction] and [strong_induction_le] in PeanoNat
    - [strong_induction_le] in BinNat
    work with the [induction] tactic. *)

From Stdlib.Arith Require Import PeanoNat.
From Stdlib.NArith Require Import BinNat.

Open Scope nat_scope.

Lemma land_diag_binary_induction_test n : Nat.land n n = n.
Proof.
  induction n as [| n IH | n IH] using Nat.binary_induction.
  - rewrite Nat.land_0_l; reflexivity.
  - rewrite Nat.land_even_l, Nat.div2_even, IH; reflexivity.
  - rewrite Nat.land_odd_l, Nat.odd_odd, Nat.div2_odd', IH; reflexivity.
Qed.

Lemma land_diag_strong_induction_test n : Nat.land n n = n.
Proof.
  induction n as [| n IH] using Nat.strong_induction_le.
  - rewrite Nat.land_0_l; reflexivity.
  - destruct (Nat.Even_or_Odd n) as [[k ->] | [k ->]].
    + rewrite <-Nat.add_1_r, Nat.land_odd_l, Nat.div2_odd', IH, Nat.odd_odd;
        [reflexivity |].
      apply Nat.le_mul_l; discriminate.
    + replace (S (2 * k + 1)) with (2 * (k + 1)); cycle 1. {
        rewrite Nat.mul_add_distr_l, <-Nat.add_succ_r, Nat.mul_1_r; reflexivity.
      }
      rewrite Nat.land_even_l, Nat.div2_even, IH; [reflexivity |].
      apply Nat.add_le_mono; [| exact (Nat.le_refl _)].
      apply Nat.le_mul_l; discriminate.
Qed.

Close Scope nat_scope.
Open Scope N_scope.

(* Of course, this example is articifial in N. However, this shows that the
   previous proof with almost no modifications. *)
Lemma land_diag_strong_induction_test_N n : N.land n n = n.
Proof.
  induction n as [| n IH] using N.strong_induction_le.
  - rewrite N.land_0_l; reflexivity.
  - destruct (N.Even_or_Odd n) as [[k ->] | [k ->]].
    + rewrite <-N.add_1_r, N.land_odd_l, N.div2_odd', IH, N.odd_odd;
        [reflexivity |].
      apply N.le_mul_l; discriminate.
    + replace (N.succ (2 * k + 1)) with (2 * (k + 1)); cycle 1. {
        rewrite N.mul_add_distr_l, <-N.add_succ_r, N.mul_1_r; reflexivity.
      }
      rewrite N.land_even_l, N.div2_even, IH; [reflexivity |].
      apply N.add_le_mono; [| exact (N.le_refl _)].
      apply N.le_mul_l; discriminate.
Qed.

(* [binary_induction] is also available for [N] *)
Lemma land_diag_binary_induction_test_N n : N.land n n = n.
Proof.
  induction n as [| n IH | n IH] using N.binary_induction.
  - rewrite N.land_0_l; reflexivity.
  - rewrite N.land_even_l, N.div2_even, IH; reflexivity.
  - rewrite N.land_odd_l, N.odd_odd, N.div2_odd', IH; reflexivity.
Qed.

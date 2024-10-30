(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Decidable PeanoNat Program.Equality.

Require Eqdep_dec.
Local Open Scope nat_scope.

Implicit Types m n x y : nat.

Theorem O_or_S n : {m : nat | S m = n} + {0 = n}.
Proof.
  induction n as [|n IHn].
  - now right.
  - left; exists n; auto.
Defined.

Notation eq_nat_dec := Nat.eq_dec (only parsing).

#[global]
Hint Resolve O_or_S eq_nat_dec: arith.

Theorem dec_eq_nat n m : decidable (n = m).
Proof.
  elim (Nat.eq_dec n m); [left|right]; trivial.
Defined.

Register dec_eq_nat as num.nat.eq_dec.

Definition UIP_nat:= Eqdep_dec.UIP_dec Nat.eq_dec.

Lemma le_unique: forall m n (le_mn1 le_mn2 : m <= n), le_mn1 = le_mn2.
Proof.
  enough (forall n m, n <= m -> forall le_mn1 le_mn2 : n <= m, le_mn1 = le_mn2) by firstorder.
  intros n m H.
  induction H as [|m H IH];
    dependent destruction le_mn1; dependent destruction le_mn2;
    try match goal with
      [ H_imp : S ?n <= ?n |- _ ] => contradiction (Nat.nle_succ_diag_l n H_imp)
    end.
  - reflexivity.
  - f_equal. apply IH.
Qed.

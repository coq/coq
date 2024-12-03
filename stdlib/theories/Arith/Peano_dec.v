(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Decidable PeanoNat.
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

Lemma le_unique: forall (m n : nat) (le_mn1 le_mn2 : m <= n), le_mn1 = le_mn2.
Proof.
  intros m. refine (le_ind_dep m _ _ _).
  - enough (forall n le_mn2 (E : m = n), le_n m = eq_rect_r _ le_mn2 E) as H.
    { intros le_mm. apply (H m le_mm eq_refl). }
    intros n le_mn2. destruct le_mn2 as [|n]; intros E.
    + replace E with (eq_refl m) by apply UIP_nat. reflexivity.
    + exfalso. apply (Nat.nle_succ_diag_l n). rewrite <- E. apply le_mn2.
  - intros n le_mn1 IH.
    enough (forall p le_mp (E : S n = p),
               le_S m n le_mn1 = eq_rect_r (le m) le_mp E) as H.
    { intros le_mp. apply (H (S n) le_mp eq_refl). }
    intros p le_mp. destruct le_mp as [|p]; intros E.
    + exfalso. apply (Nat.nle_succ_diag_l n). rewrite E. apply le_mn1.
    + injection E as E'. subst p.
      replace E with (eq_refl (S n)) by apply UIP_nat.
      compute. f_equal. apply IH.
Qed.

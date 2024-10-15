(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export PeanoNat.
Require Export Factorial.
Require Export Between.
Require Export Peano_dec.
Require Export Compare_dec.
Require Export EqNat.
Require Export Wf_nat.

(** * [arith] hint database *)

(* ** [eq_nat] *)
#[global]
Hint Resolve eq_nat_refl: arith.
#[global]
Hint Immediate eq_eq_nat eq_nat_eq: arith.

(* ** [between] *)
#[global]
Hint Resolve nth_O bet_S bet_emp bet_eq between_Sk_l exists_S exists_le
  in_int_S in_int_intro: arith.
#[global]
Hint Immediate in_int_Sp_q exists_le_S exists_S_le: arith.

(** ** [lt] and [le] *)
#[global]
Hint Resolve Nat.le_trans: arith. (* Le.le_trans *)
#[global]
Hint Immediate Nat.le_antisymm: arith. (* Le.le_antisym *)
#[global]
Hint Resolve Nat.le_0_l Nat.nle_succ_0: arith. (* Le.le_0_n Le.le_Sn_0*)
#[global]
Hint Resolve Peano.le_n_S Nat.le_succ_diag_r Nat.nle_succ_diag_l : arith. (* Le.le_n_S Le.le_n_Sn Le.le_Sn_n *)
#[local]
Definition le_n_0_eq_stt := fun n Hle => eq_sym (proj1 (Nat.le_0_r n) Hle).
Opaque le_n_0_eq_stt.
Add Search Blacklist "Coq.Arith.Arith_base.le_n_0_eq_stt".
#[global]
Hint Immediate le_n_0_eq_stt Nat.lt_le_incl Peano.le_S_n : arith. (* Le.le_n_0_eq Le.le_Sn_le Le.le_S_n *)
#[global]
Hint Resolve Nat.le_pred_l: arith. (* Le.le_pred_n *)
#[global]
Hint Resolve Nat.lt_irrefl: arith. (* Lt.lt_irrefl *)
#[local]
Definition lt_le_S_stt := fun n m => (proj2 (Nat.le_succ_l n m)).
Opaque lt_le_S_stt.
Add Search Blacklist "Coq.Arith.Arith_base.lt_le_S_stt".
#[global]
Hint Immediate lt_le_S_stt: arith. (* Lt.lt_le_S *)
#[local]
Definition lt_n_Sm_le_stt := fun n m => (proj1 (Nat.lt_succ_r n m)).
Opaque lt_n_Sm_le_stt.
Add Search Blacklist "Coq.Arith.Arith_base.lt_n_Sm_le_stt".
#[global]
Hint Immediate lt_n_Sm_le_stt: arith. (* Lt.lt_n_Sm_le *)
#[local]
Definition le_lt_n_Sm_stt := fun n m => (proj2 (Nat.lt_succ_r n m)).
Opaque le_lt_n_Sm_stt.
Add Search Blacklist "Coq.Arith.Arith_base.le_lt_n_Sm_stt".
#[global]
Hint Immediate le_lt_n_Sm_stt: arith. (* Lt.le_lt_n_Sm *)
#[local]
Definition le_not_lt_stt := fun n m => (proj1 (Nat.le_ngt n m)).
Opaque le_not_lt_stt.
Add Search Blacklist "Coq.Arith.Arith_base.le_not_lt_stt".
#[global]
Hint Immediate le_not_lt_stt: arith. (* Lt.le_not_lt *)
#[local]
Definition lt_not_le_stt := fun n m => (proj1 (Nat.lt_nge n m)).
Opaque lt_not_le_stt.
Add Search Blacklist "Coq.Arith.Arith_base.lt_not_le_stt".
#[global]
Hint Immediate lt_not_le_stt: arith. (* Lt.lt_not_le *)
#[global]
Hint Resolve Nat.lt_0_succ Nat.nlt_0_r: arith. (* Lt.lt_0_Sn Lt.lt_n_0 *)
#[local]
Definition neq_0_lt_stt := fun n Hn => proj1 (Nat.neq_0_lt_0 n) (Nat.neq_sym 0 n Hn).
Opaque neq_0_lt_stt.
Add Search Blacklist "Coq.Arith.Arith_base.neq_0_lt_stt".
#[local]
Definition lt_0_neq_stt := fun n Hlt => Nat.neq_sym n 0 (proj2 (Nat.neq_0_lt_0 n) Hlt).
Opaque lt_0_neq_stt.
Add Search Blacklist "Coq.Arith.Arith_base.lt_0_neq_stt".
#[global]
Hint Immediate neq_0_lt_stt lt_0_neq_stt: arith. (* Lt.neq_0_lt Lt.lt_0_neq *)
#[global]
Hint Resolve Nat.lt_succ_diag_r Nat.lt_lt_succ_r: arith. (* Lt.lt_n_Sn Lt.lt_S *)
#[local]
Definition lt_n_S_stt := fun n m => (proj1 (Nat.succ_lt_mono n m)).
Opaque lt_n_S_stt.
Add Search Blacklist "Coq.Arith.Arith_base.lt_n_S_stt".
#[global]
Hint Resolve lt_n_S_stt: arith. (* Lt.lt_n_S *)
#[local]
Definition lt_S_n_stt := fun n m => (proj2 (Nat.succ_lt_mono n m)).
Opaque lt_S_n_stt.
Add Search Blacklist "Coq.Arith.Arith_base.lt_S_n_stt".
#[global]
Hint Immediate lt_S_n_stt: arith. (* Lt.lt_S_n *)
#[local]
Definition lt_pred_stt := fun n m => proj1 (Nat.lt_succ_lt_pred n m).
Opaque lt_pred_stt.
Add Search Blacklist "Coq.Arith.Arith_base.lt_pred_stt".
#[global]
Hint Immediate lt_pred_stt: arith. (* Lt.lt_pred *)
#[local]
Definition lt_pred_n_n_stt := fun n Hlt => Nat.lt_pred_l n (proj2 (Nat.neq_0_lt_0 n) Hlt).
Opaque lt_pred_n_n_stt.
Add Search Blacklist "Coq.Arith.Arith_base.lt_pred_n_n_stt".
#[global]
Hint Resolve lt_pred_n_n_stt: arith. (* Lt.lt_pred_n_n *)
#[global]
Hint Resolve Nat.lt_trans Nat.lt_le_trans Nat.le_lt_trans: arith. (* Lt.lt_trans Lt.lt_le_trans Lt.le_lt_trans *)
#[global]
Hint Immediate Nat.lt_le_incl: arith. (* Lt.lt_le_weak *)
#[local]
Definition gt_Sn_O_stt : forall n, S n > 0 := Nat.lt_0_succ.
Opaque gt_Sn_O_stt.
Add Search Blacklist "Coq.Arith.Arith_base.gt_Sn_O_stt".
#[global]
Hint Resolve gt_Sn_O_stt: arith. (* Gt.gt_Sn_O *)
#[local]
Definition gt_Sn_n_stt : forall n, S n > n := Nat.lt_succ_diag_r.
Opaque gt_Sn_n_stt.
Add Search Blacklist "Coq.Arith.Arith_base.gt_Sn_n_stt".
#[global]
Hint Resolve gt_Sn_n_stt: arith. (* Gt.gt_Sn_n *)
#[local]
Definition gt_n_S_stt : forall n m, n > m -> S n > S m := fun n m Hgt => proj1 (Nat.succ_lt_mono m n) Hgt.
Opaque gt_n_S_stt.
Add Search Blacklist "Coq.Arith.Arith_base.gt_n_S_stt".
#[global]
Hint Resolve gt_n_S_stt: arith. (* Gt.gt_n_S *)
#[local]
Definition gt_S_n_stt : forall n m, S m > S n -> m > n := fun n m Hgt => proj2 (Nat.succ_lt_mono n m) Hgt.
Opaque gt_S_n_stt.
Add Search Blacklist "Coq.Arith.Arith_base.gt_S_n_stt".
#[global]
Hint Immediate gt_S_n_stt: arith. (* Gt.gt_S_n *)
#[local]
Definition gt_pred_stt : forall n m, m > S n -> pred m > n := fun n m Hgt => proj1 (Nat.lt_succ_lt_pred n m) Hgt.
Opaque gt_pred_stt.
Add Search Blacklist "Coq.Arith.Arith_base.gt_pred_stt".
#[global]
Hint Immediate gt_pred_stt: arith. (* Gt.gt_pred *)
#[local]
Definition gt_irrefl_stt : forall n, ~ n > n := Nat.lt_irrefl.
Opaque gt_irrefl_stt.
Add Search Blacklist "Coq.Arith.Arith_base.gt_irrefl_stt".
#[global]
Hint Resolve gt_irrefl_stt: arith. (* Gt.gt_irrefl *)
#[local]
Definition gt_asym_stt : forall n m, n > m -> ~ m > n := fun n m => Nat.lt_asymm m n.
Opaque gt_asym_stt.
Add Search Blacklist "Coq.Arith.Arith_base.gt_asym_stt".
#[global]
Hint Resolve gt_asym_stt: arith. (* Gt.gt_asym *)
#[local]
Definition le_not_gt_stt : forall n m, n <= m -> ~ n > m := fun n m => proj1 (Nat.le_ngt n m).
Opaque le_not_gt_stt.
Add Search Blacklist "Coq.Arith.Arith_base.le_not_gt_stt".
#[global]
Hint Resolve le_not_gt_stt: arith. (* Gt.le_not_gt *)
#[local]
Definition gt_not_le_stt: forall n m, n > m -> ~ n <= m := fun n m => proj1 (Nat.lt_nge m n).
Opaque gt_not_le_stt.
Add Search Blacklist "Coq.Arith.Arith_base.gt_not_le_stt".
#[global]
Hint Resolve gt_not_le_stt: arith. (* Gt.gt_not_le *)
#[local]
Definition le_S_gt_stt: forall n m, S n <= m -> m > n := fun n m => proj1 (Nat.le_succ_l n m).
Opaque le_S_gt_stt.
Add Search Blacklist "Coq.Arith.Arith_base.le_S_gt_stt".
#[global]
Hint Immediate le_S_gt_stt:arith. (* Gt.le_S_gt *)
#[local]
Definition gt_S_le_stt : forall n m, S m > n -> n <= m := fun n m => proj2 (Nat.succ_le_mono n m).
Opaque gt_S_le_stt.
Add Search Blacklist "Coq.Arith.Arith_base.gt_S_le_stt".
#[global]
Hint Immediate gt_S_le_stt:arith. (* Gt.gt_S_le *)
#[local]
Definition gt_le_S_stt : forall n m, m > n -> S n <= m := fun n m => proj2 (Nat.le_succ_l n m).
Opaque gt_le_S_stt.
Add Search Blacklist "Coq.Arith.Arith_base.gt_le_S_stt".
#[global]
Hint Resolve gt_le_S_stt:arith. (* Gt.gt_le_S *)
#[local]
Definition le_gt_S_stt : forall n m, n <= m -> S m > n := fun n m => proj1 (Nat.succ_le_mono n m).
Opaque le_gt_S_stt.
Add Search Blacklist "Coq.Arith.Arith_base.le_gt_S_stt".
#[global]
Hint Resolve le_gt_S_stt:arith. (* Gt.le_gt_S *)
#[local]
Definition gt_trans_S_stt : forall n m p, S n > m -> m > p -> n > p
                          := fun n m p Hgt1 Hgt2 => Nat.lt_le_trans p m n Hgt2 (proj2 (Nat.succ_le_mono _ _) Hgt1).
Opaque gt_trans_S_stt.
Add Search Blacklist "Coq.Arith.Arith_base.gt_trans_S_stt".
#[global]
Hint Resolve gt_trans_S_stt:arith. (* Gt.gt_trans_S *)
#[local]
Definition le_gt_trans_stt : forall n m p, m <= n -> m > p -> n > p
                           := fun n m p Hle Hgt => Nat.lt_le_trans p m n Hgt Hle.
Opaque le_gt_trans_stt.
Add Search Blacklist "Coq.Arith.Arith_base.le_gt_trans_stt".
#[global]
Hint Resolve le_gt_trans_stt:arith. (* Gt.le_gt_trans *)
#[local]
Definition gt_le_trans_stt : forall n m p, n > m -> p <= m -> n > p
                           := fun n m p Hgt Hle => Nat.le_lt_trans p m n Hle Hgt.
Opaque gt_le_trans_stt.
Add Search Blacklist "Coq.Arith.Arith_base.gt_le_trans_stt".
#[global]
Hint Resolve gt_le_trans_stt:arith. (* Gt.gt_le_trans *)
#[local]
Definition plus_gt_compat_l_stt : forall n m p, n > m -> p + n > p + m
                                := fun n m p Hgt => proj1 (Nat.add_lt_mono_l m n p) Hgt.
Opaque plus_gt_compat_l_stt.
Add Search Blacklist "Coq.Arith.Arith_base.plus_gt_compat_l_stt".
#[global]
Hint Resolve plus_gt_compat_l_stt:arith. (* Gt.plus_gt_compat_l *)

(* ** [add] *)
#[global]
Hint Immediate Nat.add_comm : arith. (* Plus.plus_comm *)
#[global]
Hint Resolve Nat.add_assoc : arith. (* Plus.plus_assoc *)
#[local]
Definition plus_assoc_reverse_stt := fun n m p => eq_sym (Nat.add_assoc n m p).
Opaque plus_assoc_reverse_stt.
Add Search Blacklist "Coq.Arith.Arith_base.plus_assoc_reverse_stt".
#[global]
Hint Resolve plus_assoc_reverse_stt : arith. (* Plus.plus_assoc_reverse *)
#[global]
Hint Resolve -> Nat.add_le_mono_l : arith. (* Plus.plus_le_compat_l *)
#[global]
Hint Resolve -> Nat.add_le_mono_r : arith. (* Plus.plus_le_compat_r *)
#[local]
Definition le_plus_r_stt := (fun n m => Nat.le_add_l m n).
#[local]
Definition le_plus_trans_stt := (fun n m p Hle => Nat.le_trans n _ _ Hle (Nat.le_add_r m p)).
Opaque le_plus_r_stt le_plus_trans_stt.
Add Search Blacklist "Coq.Arith.Arith_base.le_plus_r_stt".
Add Search Blacklist "Coq.Arith.Arith_base.le_plus_trans_stt".
#[global]
Hint Resolve Nat.le_add_r le_plus_r_stt le_plus_trans_stt : arith. (* Plus.le_plus_l Plus.le_plus_r_stt Plus.le_plus_trans_stt *)
#[local]
Definition lt_plus_trans_stt := (fun n m p Hlt => Nat.lt_le_trans n _ _ Hlt (Nat.le_add_r m p)).
Opaque lt_plus_trans_stt.
Add Search Blacklist "Coq.Arith.Arith_base.lt_plus_trans_stt".
#[global]
Hint Immediate lt_plus_trans_stt : arith. (* Plus.lt_plus_trans_stt *)
#[global]
Hint Resolve -> Nat.add_lt_mono_l : arith. (* Plus_lt_compat_l *)
#[global]
Hint Resolve -> Nat.add_lt_mono_r : arith. (* Plus_lt_compat_r *)


(* ** [sub] *)
#[local]
Definition minus_n_O_stt := fun n => eq_sym (Nat.sub_0_r n).
Opaque minus_n_O_stt.
Add Search Blacklist "Coq.Arith.Arith_base.minus_n_O_stt".
#[global]
Hint Resolve minus_n_O_stt: arith. (* Minus.minus_n_O *)
#[local]
Definition minus_Sn_m_stt := fun n m Hle => eq_sym (Nat.sub_succ_l m n Hle).
Opaque minus_Sn_m_stt.
Add Search Blacklist "Coq.Arith.Arith_base.minus_Sn_m_stt".
#[global]
Hint Resolve minus_Sn_m_stt: arith. (* Minus.minus_Sn_m *)
#[local]
Definition minus_diag_reverse_stt := fun n => eq_sym (Nat.sub_diag n).
Opaque minus_diag_reverse_stt.
Add Search Blacklist "Coq.Arith.Arith_base.minus_diag_reverse_stt".
#[global]
Hint Resolve minus_diag_reverse_stt: arith. (* Minus.minus_diag_reverse *)
#[local]
Lemma minus_plus_simpl_l_reverse_stt n m p : n - m = p + n - (p + m).
Proof.
 now rewrite Nat.sub_add_distr, Nat.add_comm, Nat.add_sub.
Qed.
Add Search Blacklist "Coq.Arith.Arith_base.minus_plus_simpl_l_reverse_stt".
#[global]
Hint Resolve minus_plus_simpl_l_reverse_stt: arith. (* Minus.minus_plus_simpl_l_reverse *)
#[local]
Definition plus_minus_stt := fun n m p Heq => eq_sym (Nat.add_sub_eq_l n m p (eq_sym Heq)).
Opaque plus_minus_stt.
Add Search Blacklist "Coq.Arith.Arith_base.plus_minus_stt".
#[global]
Hint Immediate plus_minus_stt: arith. (* Minus.plus_minus *)
#[local]
Definition minus_plus_stt := (fun n m => eq_ind _ (fun x => x - n = m) (Nat.add_sub m n) _ (Nat.add_comm _ _)).
Opaque minus_plus_stt.
Add Search Blacklist "Coq.Arith.Arith_base.minus_plus_stt".
#[global]
Hint Resolve minus_plus_stt: arith. (* Minus.minus_plus *)
#[local]
Definition le_plus_minus_stt := fun n m Hle => eq_sym (eq_trans (Nat.add_comm _ _) (Nat.sub_add n m Hle)).
Opaque le_plus_minus_stt.
Add Search Blacklist "Coq.Arith.Arith_base.le_plus_minus_stt".
#[global]
Hint Resolve le_plus_minus_stt: arith. (* Minus.le_plus_minus *)
#[local]
Definition le_plus_minus_r_stt := fun n m Hle => eq_trans (Nat.add_comm _ _) (Nat.sub_add n m Hle).
Opaque le_plus_minus_r_stt.
Add Search Blacklist "Coq.Arith.Arith_base.le_plus_minus_r_stt".
#[global]
Hint Resolve le_plus_minus_r_stt: arith. (* Minus.le_plus_minus_r *)
#[global]
Hint Resolve Nat.sub_lt: arith. (* Minus.lt_minus *)
#[local]
Definition lt_O_minus_lt_stt : forall n m, 0 < n - m -> m < n
                            := fun n m => proj2 (Nat.lt_add_lt_sub_r 0 n m).
Opaque lt_O_minus_lt_stt.
Add Search Blacklist "Coq.Arith.Arith_base.lt_O_minus_lt_stt".
#[global]
Hint Immediate lt_O_minus_lt_stt: arith. (* Minus.lt_O_minus_lt *)

(* ** [mul] *)
#[global]
Hint Resolve Nat.mul_1_l Nat.mul_1_r: arith. (* Mult.mult_1_l Mult.mult_1_r *)
#[global]
Hint Resolve Nat.mul_comm: arith. (* Mult.mult_comm *)
#[global]
Hint Resolve Nat.mul_add_distr_r: arith. (* Mult.mult_plus_distr_r *)
#[global]
Hint Resolve Nat.mul_sub_distr_r: arith. (* Mult.mult_minus_distr_r *)
#[global]
Hint Resolve Nat.mul_sub_distr_l: arith. (* Mult.mult_minus_distr_l *)
#[local]
Definition mult_assoc_reverse_stt := fun n m p => eq_sym (Nat.mul_assoc n m p).
Opaque mult_assoc_reverse_stt.
Add Search Blacklist "Coq.Arith.Arith_base.mult_assoc_reverse_stt".
#[global]
Hint Resolve mult_assoc_reverse_stt Nat.mul_assoc: arith. (* Mult.mult_assoc_reverse Mult.mult_assoc *)
#[local]
Lemma mult_O_le_stt n m : m = 0 \/ n <= m * n.
Proof.
 destruct m; [left|right]; simpl; trivial using Nat.le_add_r.
Qed.
Add Search Blacklist "Coq.Arith.Arith_base.mult_O_le_stt".
#[global]
Hint Resolve mult_O_le_stt: arith. (* Mult.mult_O_le *)
#[global]
Hint Resolve Nat.mul_le_mono_l: arith. (* Mult.mult_le_compat_l *)
#[local]
Definition mult_S_lt_compat_l_stt := (fun n m p Hlt => proj1 (Nat.mul_lt_mono_pos_l (S n) m p (Nat.lt_0_succ n)) Hlt).
Opaque mult_S_lt_compat_l_stt.
Add Search Blacklist "Coq.Arith.Arith_base.mult_S_lt_compat_l_stt".
#[global]
Hint Resolve mult_S_lt_compat_l_stt: arith. (* Mult.mult_S_lt_compat_l *)

(* ** [min] and [max] *)
#[global]
Hint Resolve Nat.max_l Nat.max_r Nat.le_max_l Nat.le_max_r: arith.
#[global]
Hint Resolve Nat.min_l Nat.min_r Nat.le_min_l Nat.le_min_r: arith.

(* ** [Even_alt] and [Odd_alt] *)
#[global]
Hint Constructors Nat.Even_alt: arith.
#[global]
Hint Constructors Nat.Odd_alt: arith.

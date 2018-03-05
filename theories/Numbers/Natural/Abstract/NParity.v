(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Bool NSub NZParity.

(** Some additional properties of [even], [odd]. *)

Module Type NParityProp (Import N : NAxiomsSig')(Import NP : NSubProp N).

Include NZParityProp N N NP.

Lemma odd_pred : forall n, n~=0 -> odd (P n) = even n.
Proof.
 intros. rewrite <- (succ_pred n) at 2 by trivial.
 symmetry. apply even_succ.
Qed.

Lemma even_pred : forall n, n~=0 -> even (P n) = odd n.
Proof.
 intros. rewrite <- (succ_pred n) at 2 by trivial.
 symmetry. apply odd_succ.
Qed.

Lemma even_sub : forall n m, m<=n -> even (n-m) = Bool.eqb (even n) (even m).
Proof.
 intros.
 case_eq (even n); case_eq (even m);
  rewrite <- ?negb_true_iff, ?negb_even, ?odd_spec, ?even_spec;
  intros (m',Hm) (n',Hn).
 exists (n'-m'). now rewrite mul_sub_distr_l, Hn, Hm.
 exists (n'-m'-1).
  rewrite !mul_sub_distr_l, Hn, Hm, sub_add_distr, mul_1_r.
  rewrite two_succ at 5. rewrite <- (add_1_l 1). rewrite sub_add_distr.
  symmetry. apply sub_add.
  apply le_add_le_sub_l.
  rewrite add_1_l, <- two_succ, <- (mul_1_r 2) at 1.
  rewrite <- mul_sub_distr_l. rewrite <- mul_le_mono_pos_l by order'.
  rewrite one_succ, le_succ_l. rewrite <- lt_add_lt_sub_l, add_0_r.
  destruct (le_gt_cases n' m') as [LE|GT]; trivial.
  generalize (double_below _ _ LE). order.
 exists (n'-m'). rewrite mul_sub_distr_l, Hn, Hm.
  apply add_sub_swap.
  apply mul_le_mono_pos_l; try order'.
  destruct (le_gt_cases m' n') as [LE|GT]; trivial.
  generalize (double_above _ _ GT). order.
 exists (n'-m'). rewrite Hm,Hn, mul_sub_distr_l.
  rewrite sub_add_distr. rewrite add_sub_swap. apply add_sub.
  apply succ_le_mono.
  rewrite add_1_r in Hm,Hn. order.
Qed.

Lemma odd_sub : forall n m, m<=n -> odd (n-m) = xorb (odd n) (odd m).
Proof.
 intros. rewrite <- !negb_even. rewrite even_sub by trivial.
 now destruct (even n), (even m).
Qed.

End NParityProp.

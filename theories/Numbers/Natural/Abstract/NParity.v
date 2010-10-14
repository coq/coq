(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Bool NSub.

(** Properties of [even], [odd]. *)

(** NB: most parts of [NParity] and [ZParity] are common,
    but it is difficult to share them in NZ, since
    initial proofs [Even_or_Odd] and [Even_Odd_False] must
    be proved differently *)

Module Type NParityProp (Import N : NAxiomsSig')(Import NP : NSubProp N).

Instance Even_wd : Proper (eq==>iff) Even.
Proof. unfold Even. solve_predicate_wd. Qed.

Instance Odd_wd : Proper (eq==>iff) Odd.
Proof. unfold Odd. solve_predicate_wd. Qed.

Instance even_wd : Proper (eq==>Logic.eq) even.
Proof.
 intros x x' EQ. rewrite eq_iff_eq_true, 2 even_spec. now apply Even_wd.
Qed.

Instance odd_wd : Proper (eq==>Logic.eq) odd.
Proof.
 intros x x' EQ. rewrite eq_iff_eq_true, 2 odd_spec. now apply Odd_wd.
Qed.

Lemma Even_or_Odd : forall x, Even x \/ Odd x.
Proof.
 induct x.
 left. exists 0. now nzsimpl.
 intros x.
 intros [(y,H)|(y,H)].
 right. exists y. rewrite H. now nzsimpl.
 left. exists (S y). rewrite H. now nzsimpl.
Qed.

Lemma double_below : forall n m, n<=m -> 2*n < 2*m+1.
Proof.
 intros. nzsimpl. apply lt_succ_r. now apply add_le_mono.
Qed.

Lemma double_above : forall n m, n<m -> 2*n+1 < 2*m.
Proof.
 intros. nzsimpl.
 rewrite <- le_succ_l, <- add_succ_l, <- add_succ_r.
 apply add_le_mono; now apply le_succ_l.
Qed.

Lemma Even_Odd_False : forall x, Even x -> Odd x -> False.
Proof.
intros x (y,E) (z,O). rewrite O in E; clear O.
destruct (le_gt_cases y z) as [LE|GT].
generalize (double_below _ _ LE); order.
generalize (double_above _ _ GT); order.
Qed.

Lemma orb_even_odd : forall n, orb (even n) (odd n) = true.
Proof.
 intros.
 destruct (Even_or_Odd n) as [H|H].
 rewrite <- even_spec in H. now rewrite H.
 rewrite <- odd_spec in H. now rewrite H, orb_true_r.
Qed.

Lemma negb_odd_even : forall n, negb (odd n) = even n.
Proof.
 intros.
 generalize (Even_or_Odd n) (Even_Odd_False n).
 rewrite <- even_spec, <- odd_spec.
 destruct (odd n), (even n); simpl; intuition.
Qed.

Lemma negb_even_odd : forall n, negb (even n) = odd n.
Proof.
 intros. rewrite <- negb_odd_even. apply negb_involutive.
Qed.

Lemma even_0 : even 0 = true.
Proof.
 rewrite even_spec. exists 0. now nzsimpl.
Qed.

Lemma odd_1 : odd 1 = true.
Proof.
 rewrite odd_spec. exists 0. now nzsimpl.
Qed.

Lemma Odd_succ_Even : forall n, Odd (S n) <-> Even n.
Proof.
 split; intros (m,H).
 exists m. apply succ_inj. now rewrite add_1_r in H.
 exists m. rewrite add_1_r. now apply succ_wd.
Qed.

Lemma odd_succ_even : forall n, odd (S n) = even n.
Proof.
 intros. apply eq_iff_eq_true. rewrite even_spec, odd_spec.
 apply Odd_succ_Even.
Qed.

Lemma even_succ_odd : forall n, even (S n) = odd n.
Proof.
 intros. now rewrite <- negb_odd_even, odd_succ_even, negb_even_odd.
Qed.

Lemma Even_succ_Odd : forall n, Even (S n) <-> Odd n.
Proof.
 intros. now rewrite <- even_spec, even_succ_odd, odd_spec.
Qed.

Lemma odd_pred_even : forall n, n~=0 -> odd (P n) = even n.
Proof.
 intros. rewrite <- (succ_pred n) at 2 by trivial.
 symmetry. apply even_succ_odd.
Qed.

Lemma even_pred_odd : forall n, n~=0 -> even (P n) = odd n.
Proof.
 intros. rewrite <- (succ_pred n) at 2 by trivial.
 symmetry. apply odd_succ_even.
Qed.

Lemma even_add : forall n m, even (n+m) = Bool.eqb (even n) (even m).
Proof.
 intros.
 case_eq (even n); case_eq (even m);
  rewrite <- ?negb_true_iff, ?negb_even_odd, ?odd_spec, ?even_spec;
  intros (m',Hm) (n',Hn).
 exists (n'+m'). now rewrite mul_add_distr_l, Hn, Hm.
 exists (n'+m'). now rewrite mul_add_distr_l, Hn, Hm, add_assoc.
 exists (n'+m'). now rewrite mul_add_distr_l, Hn, Hm, add_shuffle0.
 exists (n'+m'+1). rewrite Hm,Hn. nzsimpl. now rewrite add_shuffle1.
Qed.

Lemma odd_add : forall n m, odd (n+m) = xorb (odd n) (odd m).
Proof.
 intros. rewrite <- !negb_even_odd. rewrite even_add.
 now destruct (even n), (even m).
Qed.

Lemma even_mul : forall n m, even (mul n m) = even n || even m.
Proof.
 intros.
 case_eq (even n); simpl; rewrite ?even_spec.
 intros (n',Hn). exists (n'*m). now rewrite Hn, mul_assoc.
 case_eq (even m); simpl; rewrite ?even_spec.
 intros (m',Hm). exists (n*m'). now rewrite Hm, !mul_assoc, (mul_comm 2).
 (* odd / odd *)
 rewrite <- !negb_true_iff, !negb_even_odd, !odd_spec.
 intros (m',Hm) (n',Hn). exists (n'*2*m' +n'+m').
 rewrite Hn,Hm, !mul_add_distr_l, !mul_add_distr_r, !mul_1_l, !mul_1_r.
 now rewrite add_shuffle1, add_assoc, !mul_assoc.
Qed.

Lemma odd_mul : forall n m, odd (mul n m) = odd n && odd m.
Proof.
 intros. rewrite <- !negb_even_odd. rewrite even_mul.
 now destruct (even n), (even m).
Qed.

Lemma even_sub : forall n m, m<=n -> even (n-m) = Bool.eqb (even n) (even m).
Proof.
 intros.
 case_eq (even n); case_eq (even m);
  rewrite <- ?negb_true_iff, ?negb_even_odd, ?odd_spec, ?even_spec;
  intros (m',Hm) (n',Hn).
 exists (n'-m'). now rewrite mul_sub_distr_l, Hn, Hm.
 exists (n'-m'-1).
  rewrite !mul_sub_distr_l, Hn, Hm, sub_add_distr, mul_1_r.
  rewrite <- (add_1_l 1) at 5. rewrite sub_add_distr.
  symmetry. apply sub_add.
  apply le_add_le_sub_l.
  rewrite add_1_l, <- (mul_1_r 2) at 1.
  rewrite <- mul_sub_distr_l. rewrite <- mul_le_mono_pos_l.
  rewrite le_succ_l. rewrite <- lt_add_lt_sub_l, add_0_r.
  destruct (le_gt_cases n' m') as [LE|GT]; trivial.
  generalize (double_below _ _ LE). order.
  apply lt_succ_r, le_0_1.
 exists (n'-m'). rewrite mul_sub_distr_l, Hn, Hm.
  apply add_sub_swap.
  apply mul_le_mono_pos_l.
  apply lt_succ_r, le_0_1.
  destruct (le_gt_cases m' n') as [LE|GT]; trivial.
  generalize (double_above _ _ GT). order.
 exists (n'-m'). rewrite Hm,Hn, mul_sub_distr_l.
  rewrite sub_add_distr. rewrite add_sub_swap. apply add_sub.
  apply succ_le_mono.
  rewrite add_1_r in Hm,Hn. order.
Qed.

Lemma odd_sub : forall n m, m<=n -> odd (n-m) = xorb (odd n) (odd m).
Proof.
 intros. rewrite <- !negb_even_odd. rewrite even_sub by trivial.
 now destruct (even n), (even m).
Qed.

End NParityProp.

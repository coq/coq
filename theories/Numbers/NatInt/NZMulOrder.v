(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Import NZAxioms.
Require Import NZAddOrder.

Module Type NZMulOrderProp (Import NZ : NZOrdAxiomsSig').
Include NZAddOrderProp NZ.

Theorem mul_lt_pred :
  forall p q n m, S p == q -> (p * n < p * m <-> q * n + m < q * m + n).
Proof.
intros p q n m H. rewrite <- H. nzsimpl.
rewrite <- ! add_assoc, (add_comm n m).
now rewrite <- add_lt_mono_r.
Qed.

Theorem mul_lt_mono_pos_l : forall p n m, 0 < p -> (n < m <-> p * n < p * m).
Proof.
intros p n m Hp. revert n m. apply lt_ind with (4:=Hp). solve_proper.
intros. now nzsimpl.
clear p Hp. intros p Hp IH n m. nzsimpl.
assert (LR : forall n m, n < m -> p * n + n < p * m + m)
 by (intros n1 m1 H; apply add_lt_mono; trivial; now rewrite <- IH).
split; intros H.
now apply LR.
destruct (lt_trichotomy n m) as [LT|[EQ|GT]]; trivial.
rewrite EQ in H. order.
apply LR in GT. order.
Qed.

Theorem mul_lt_mono_pos_r : forall p n m, 0 < p -> (n < m <-> n * p < m * p).
Proof.
intros p n m.
rewrite (mul_comm n p), (mul_comm m p). now apply mul_lt_mono_pos_l.
Qed.

Theorem mul_lt_mono_neg_l : forall p n m, p < 0 -> (n < m <-> p * m < p * n).
Proof.
nzord_induct p.
order.
intros p Hp _ n m Hp'. apply lt_succ_l in Hp'. order.
intros p Hp IH n m _. apply le_succ_l in Hp.
le_elim Hp.
assert (LR : forall n m, n < m -> p * m < p * n).
 intros n1 m1 H. apply (le_lt_add_lt n1 m1).
 now apply lt_le_incl. rewrite <- 2 mul_succ_l. now rewrite <- IH.
split; intros H.
now apply LR.
destruct (lt_trichotomy n m) as [LT|[EQ|GT]]; trivial.
rewrite EQ in H. order.
apply LR in GT. order.
rewrite (mul_lt_pred p (S p)), Hp; now nzsimpl.
Qed.

Theorem mul_lt_mono_neg_r : forall p n m, p < 0 -> (n < m <-> m * p < n * p).
Proof.
intros p n m.
rewrite (mul_comm n p), (mul_comm m p). now apply mul_lt_mono_neg_l.
Qed.

Theorem mul_le_mono_nonneg_l : forall n m p, 0 <= p -> n <= m -> p * n <= p * m.
Proof.
intros n m p H1 H2. le_elim H1.
le_elim H2. apply lt_le_incl. now apply mul_lt_mono_pos_l.
apply eq_le_incl; now rewrite H2.
apply eq_le_incl; rewrite <- H1; now do 2 rewrite mul_0_l.
Qed.

Theorem mul_le_mono_nonpos_l : forall n m p, p <= 0 -> n <= m -> p * m <= p * n.
Proof.
intros n m p H1 H2. le_elim H1.
le_elim H2. apply lt_le_incl. now apply mul_lt_mono_neg_l.
apply eq_le_incl; now rewrite H2.
apply eq_le_incl; rewrite H1; now do 2 rewrite mul_0_l.
Qed.

Theorem mul_le_mono_nonneg_r : forall n m p, 0 <= p -> n <= m -> n * p <= m * p.
Proof.
intros n m p H1 H2;
rewrite (mul_comm n p), (mul_comm m p); now apply mul_le_mono_nonneg_l.
Qed.

Theorem mul_le_mono_nonpos_r : forall n m p, p <= 0 -> n <= m -> m * p <= n * p.
Proof.
intros n m p H1 H2;
rewrite (mul_comm n p), (mul_comm m p); now apply mul_le_mono_nonpos_l.
Qed.

Theorem mul_cancel_l : forall n m p, p ~= 0 -> (p * n == p * m <-> n == m).
Proof.
intros n m p Hp; split; intro H; [|now f_equiv].
apply lt_gt_cases in Hp; destruct Hp as [Hp|Hp];
 destruct (lt_trichotomy n m) as [LT|[EQ|GT]]; trivial.
apply (mul_lt_mono_neg_l p) in LT; order.
apply (mul_lt_mono_neg_l p) in GT; order.
apply (mul_lt_mono_pos_l p) in LT; order.
apply (mul_lt_mono_pos_l p) in GT; order.
Qed.

Theorem mul_cancel_r : forall n m p, p ~= 0 -> (n * p == m * p <-> n == m).
Proof.
intros n m p. rewrite (mul_comm n p), (mul_comm m p); apply mul_cancel_l.
Qed.

Theorem mul_id_l : forall n m, m ~= 0 -> (n * m == m <-> n == 1).
Proof.
intros n m H.
stepl (n * m == 1 * m) by now rewrite mul_1_l. now apply mul_cancel_r.
Qed.

Theorem mul_id_r : forall n m, n ~= 0 -> (n * m == n <-> m == 1).
Proof.
intros n m; rewrite mul_comm; apply mul_id_l.
Qed.

Theorem mul_le_mono_pos_l : forall n m p, 0 < p -> (n <= m <-> p * n <= p * m).
Proof.
intros n m p H; do 2 rewrite lt_eq_cases.
rewrite (mul_lt_mono_pos_l p n m) by assumption.
now rewrite -> (mul_cancel_l n m p) by
(intro H1; rewrite H1 in H; false_hyp H lt_irrefl).
Qed.

Theorem mul_le_mono_pos_r : forall n m p, 0 < p -> (n <= m <-> n * p <= m * p).
Proof.
intros n m p. rewrite (mul_comm n p), (mul_comm m p); apply mul_le_mono_pos_l.
Qed.

Theorem mul_le_mono_neg_l : forall n m p, p < 0 -> (n <= m <-> p * m <= p * n).
Proof.
intros n m p H; do 2 rewrite lt_eq_cases.
rewrite (mul_lt_mono_neg_l p n m); [| assumption].
rewrite -> (mul_cancel_l m n p)
 by (intro H1; rewrite H1 in H; false_hyp H lt_irrefl).
now setoid_replace (n == m) with (m == n) by (split; now intro).
Qed.

Theorem mul_le_mono_neg_r : forall n m p, p < 0 -> (n <= m <-> m * p <= n * p).
Proof.
intros n m p. rewrite (mul_comm n p), (mul_comm m p); apply mul_le_mono_neg_l.
Qed.

Theorem mul_lt_mono_nonneg :
  forall n m p q, 0 <= n -> n < m -> 0 <= p -> p < q -> n * p < m * q.
Proof.
intros n m p q H1 H2 H3 H4.
apply le_lt_trans with (m * p).
apply mul_le_mono_nonneg_r; [assumption | now apply lt_le_incl].
apply -> mul_lt_mono_pos_l; [assumption | now apply le_lt_trans with n].
Qed.

(* There are still many variants of the theorem above. One can assume 0 < n
or 0 < p or n <= m or p <= q. *)

Theorem mul_le_mono_nonneg :
  forall n m p q, 0 <= n -> n <= m -> 0 <= p -> p <= q -> n * p <= m * q.
Proof.
intros n m p q H1 H2 H3 H4.
le_elim H2; le_elim H4.
apply lt_le_incl; now apply mul_lt_mono_nonneg.
rewrite <- H4; apply mul_le_mono_nonneg_r; [assumption | now apply lt_le_incl].
rewrite <- H2; apply mul_le_mono_nonneg_l; [assumption | now apply lt_le_incl].
rewrite H2; rewrite H4; now apply eq_le_incl.
Qed.

Theorem mul_pos_pos : forall n m, 0 < n -> 0 < m -> 0 < n * m.
Proof.
intros n m H1 H2. rewrite <- (mul_0_l m). now apply mul_lt_mono_pos_r.
Qed.

Theorem mul_neg_neg : forall n m, n < 0 -> m < 0 -> 0 < n * m.
Proof.
intros n m H1 H2. rewrite <- (mul_0_l m). now apply mul_lt_mono_neg_r.
Qed.

Theorem mul_pos_neg : forall n m, 0 < n -> m < 0 -> n * m < 0.
Proof.
intros n m H1 H2. rewrite <- (mul_0_l m). now apply mul_lt_mono_neg_r.
Qed.

Theorem mul_neg_pos : forall n m, n < 0 -> 0 < m -> n * m < 0.
Proof.
intros; rewrite mul_comm; now apply mul_pos_neg.
Qed.

Theorem mul_nonneg_nonneg : forall n m, 0 <= n -> 0 <= m -> 0 <= n*m.
Proof.
intros. rewrite <- (mul_0_l m). apply mul_le_mono_nonneg; order.
Qed.

Theorem mul_pos_cancel_l : forall n m, 0 < n -> (0 < n*m <-> 0 < m).
Proof.
intros n m Hn. rewrite <- (mul_0_r n) at 1.
 symmetry. now apply mul_lt_mono_pos_l.
Qed.

Theorem mul_pos_cancel_r : forall n m, 0 < m -> (0 < n*m <-> 0 < n).
Proof.
intros n m Hn. rewrite <- (mul_0_l m) at 1.
 symmetry. now apply mul_lt_mono_pos_r.
Qed.

Theorem mul_nonneg_cancel_l : forall n m, 0 < n -> (0 <= n*m <-> 0 <= m).
Proof.
intros n m Hn. rewrite <- (mul_0_r n) at 1.
 symmetry. now apply mul_le_mono_pos_l.
Qed.

Theorem mul_nonneg_cancel_r : forall n m, 0 < m -> (0 <= n*m <-> 0 <= n).
Proof.
intros n m Hn. rewrite <- (mul_0_l m) at 1.
 symmetry. now apply mul_le_mono_pos_r.
Qed.

Theorem lt_1_mul_pos : forall n m, 1 < n -> 0 < m -> 1 < n * m.
Proof.
intros n m H1 H2. apply (mul_lt_mono_pos_r m) in H1.
rewrite mul_1_l in H1. now apply lt_1_l with m.
assumption.
Qed.

Theorem eq_mul_0 : forall n m, n * m == 0 <-> n == 0 \/ m == 0.
Proof.
intros n m; split.
intro H; destruct (lt_trichotomy n 0) as [H1 | [H1 | H1]];
destruct (lt_trichotomy m 0) as [H2 | [H2 | H2]];
try (now right); try (now left).
exfalso; now apply (lt_neq 0 (n * m)); [apply mul_neg_neg |].
exfalso; now apply (lt_neq (n * m) 0); [apply mul_neg_pos |].
exfalso; now apply (lt_neq (n * m) 0); [apply mul_pos_neg |].
exfalso; now apply (lt_neq 0 (n * m)); [apply mul_pos_pos |].
intros [H | H]. now rewrite H, mul_0_l. now rewrite H, mul_0_r.
Qed.

Theorem neq_mul_0 : forall n m, n ~= 0 /\ m ~= 0 <-> n * m ~= 0.
Proof.
intros n m; split; intro H.
intro H1; apply eq_mul_0 in H1. tauto.
split; intro H1; rewrite H1 in H;
(rewrite mul_0_l in H || rewrite mul_0_r in H); now apply H.
Qed.

Theorem eq_square_0 : forall n, n * n == 0 <-> n == 0.
Proof.
intro n; rewrite eq_mul_0; tauto.
Qed.

Theorem eq_mul_0_l : forall n m, n * m == 0 -> m ~= 0 -> n == 0.
Proof.
intros n m H1 H2. apply eq_mul_0 in H1. destruct H1 as [H1 | H1].
assumption. false_hyp H1 H2.
Qed.

Theorem eq_mul_0_r : forall n m, n * m == 0 -> n ~= 0 -> m == 0.
Proof.
intros n m H1 H2; apply eq_mul_0 in H1. destruct H1 as [H1 | H1].
false_hyp H1 H2. assumption.
Qed.

(** Some alternative names: *)

Definition mul_eq_0 := eq_mul_0.
Definition mul_eq_0_l := eq_mul_0_l.
Definition mul_eq_0_r := eq_mul_0_r.

Theorem lt_0_mul n m : 0 < n * m <-> (0 < n /\ 0 < m) \/ (m < 0 /\ n < 0).
Proof.
split; [intro H | intros [[H1 H2] | [H1 H2]]].
destruct (lt_trichotomy n 0) as [H1 | [H1 | H1]];
[| rewrite H1 in H; rewrite mul_0_l in H; false_hyp H lt_irrefl |];
(destruct (lt_trichotomy m 0) as [H2 | [H2 | H2]];
[| rewrite H2 in H; rewrite mul_0_r in H; false_hyp H lt_irrefl |]);
try (left; now split); try (right; now split).
assert (H3 : n * m < 0) by now apply mul_neg_pos.
exfalso; now apply (lt_asymm (n * m) 0).
assert (H3 : n * m < 0) by now apply mul_pos_neg.
exfalso; now apply (lt_asymm (n * m) 0).
now apply mul_pos_pos. now apply mul_neg_neg.
Qed.

Theorem square_lt_mono_nonneg : forall n m, 0 <= n -> n < m -> n * n < m * m.
Proof.
intros n m H1 H2. now apply mul_lt_mono_nonneg.
Qed.

Theorem square_le_mono_nonneg : forall n m, 0 <= n -> n <= m -> n * n <= m * m.
Proof.
intros n m H1 H2. now apply mul_le_mono_nonneg.
Qed.

(* The converse theorems require nonnegativity (or nonpositivity) of the
other variable *)

Theorem square_lt_simpl_nonneg : forall n m, 0 <= m -> n * n < m * m -> n < m.
Proof.
intros n m H1 H2. destruct (lt_ge_cases n 0).
now apply lt_le_trans with 0.
destruct (lt_ge_cases n m) as [LT|LE]; trivial.
apply square_le_mono_nonneg in LE; order.
Qed.

Theorem square_le_simpl_nonneg : forall n m, 0 <= m -> n * n <= m * m -> n <= m.
Proof.
intros n m H1 H2. destruct (lt_ge_cases n 0).
apply lt_le_incl; now apply lt_le_trans with 0.
destruct (le_gt_cases n m) as [LE|LT]; trivial.
apply square_lt_mono_nonneg in LT; order.
Qed.

Theorem mul_2_mono_l : forall n m, n < m -> 1 + 2 * n < 2 * m.
Proof.
intros n m. rewrite <- le_succ_l, (mul_le_mono_pos_l (S n) m two).
rewrite two_succ. nzsimpl. now rewrite le_succ_l.
order'.
Qed.

Lemma add_le_mul : forall a b, 1<a -> 1<b -> a+b <= a*b.
Proof.
 assert (AUX : forall a b, 0<a -> 0<b -> (S a)+(S b) <= (S a)*(S b)).
  intros a b Ha Hb.
  nzsimpl. rewrite <- succ_le_mono. apply le_succ_l.
  rewrite <- add_assoc, <- (add_0_l (a+b)), (add_comm b).
  apply add_lt_mono_r.
  now apply mul_pos_pos.
 intros a b Ha Hb.
 assert (Ha' := lt_succ_pred 1 a Ha).
 assert (Hb' := lt_succ_pred 1 b Hb).
 rewrite <- Ha', <- Hb'. apply AUX; rewrite succ_lt_mono, <- one_succ; order.
Qed.

(** A few results about squares *)

Lemma square_nonneg : forall a, 0 <= a * a.
Proof.
 intros. rewrite <- (mul_0_r a). destruct (le_gt_cases a 0).
 now apply mul_le_mono_nonpos_l.
 apply mul_le_mono_nonneg_l; order.
Qed.

Lemma crossmul_le_addsquare : forall a b, 0<=a -> 0<=b -> b*a+a*b <= a*a+b*b.
Proof.
 assert (AUX : forall a b, 0<=a<=b -> b*a+a*b <= a*a+b*b).
  intros a b (Ha,H).
  destruct (le_exists_sub _ _ H) as (d & EQ & Hd).
  rewrite EQ.
  rewrite 2 mul_add_distr_r.
  rewrite !add_assoc. apply add_le_mono_r.
  rewrite add_comm. apply add_le_mono_l.
  apply mul_le_mono_nonneg_l; trivial. order.
 intros a b Ha Hb.
 destruct (le_gt_cases a b).
 apply AUX; split; order.
 rewrite (add_comm (b*a)), (add_comm (a*a)).
 apply AUX; split; order.
Qed.

Lemma add_square_le : forall a b, 0<=a -> 0<=b ->
 a*a + b*b <= (a+b)*(a+b).
Proof.
 intros a b Ha Hb.
 rewrite mul_add_distr_r, !mul_add_distr_l.
 rewrite add_assoc.
 apply add_le_mono_r.
 rewrite <- add_assoc.
 rewrite <- (add_0_r (a*a)) at 1.
 apply add_le_mono_l.
 apply add_nonneg_nonneg; now apply mul_nonneg_nonneg.
Qed.

Lemma square_add_le : forall a b, 0<=a -> 0<=b ->
 (a+b)*(a+b) <= 2*(a*a + b*b).
Proof.
 intros a b Ha Hb.
 rewrite !mul_add_distr_l, !mul_add_distr_r. nzsimpl'.
 rewrite <- !add_assoc. apply add_le_mono_l.
 rewrite !add_assoc. apply add_le_mono_r.
 apply crossmul_le_addsquare; order.
Qed.

Lemma quadmul_le_squareadd : forall a b, 0<=a -> 0<=b ->
 2*2*a*b <= (a+b)*(a+b).
Proof.
 intros.
 nzsimpl'.
 rewrite !mul_add_distr_l, !mul_add_distr_r.
 rewrite (add_comm _ (b*b)), add_assoc.
 apply add_le_mono_r.
 rewrite (add_shuffle0 (a*a)), (mul_comm b a).
 apply add_le_mono_r.
 rewrite (mul_comm a b) at 1.
 now apply crossmul_le_addsquare.
Qed.

End NZMulOrderProp.

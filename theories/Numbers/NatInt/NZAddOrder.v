(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

(**
* Properties of orders and addition for modules implementing [NZOrdAxiomsSig']

This file defines the [NZAddOrderProp] functor type, meant to be [Include]d
in a module implementing [NZOrdAxiomsSig'] (see [Coq.Numbers.NatInt.NZAxioms]).

This gives important basic compatibility lemmas between [add] and [lt], [le].

In the second part of this file, we further assume [IsNatInt] and prove
results about subtraction which are shared between integers and natural numbers.
*)
From Coq.Numbers.NatInt Require Import NZAxioms NZBase NZMul NZOrder.

Module Type NZAddOrderProp (Import NZ : NZOrdAxiomsSig').
Include NZBaseProp NZ <+ NZMulProp NZ <+ NZOrderProp NZ.

Theorem add_lt_mono_l : forall n m p, n < m <-> p + n < p + m.
Proof.
  intros n m p; nzinduct p. - now nzsimpl.
  - intro p. nzsimpl. now rewrite <- succ_lt_mono.
Qed.

Theorem add_lt_mono_r : forall n m p, n < m <-> n + p < m + p.
Proof.
intros n m p. rewrite (add_comm n p), (add_comm m p); apply add_lt_mono_l.
Qed.

Theorem add_lt_mono : forall n m p q, n < m -> p < q -> n + p < m + q.
Proof.
intros n m p q H1 H2.
apply lt_trans with (m + p);
[now apply add_lt_mono_r | now apply add_lt_mono_l].
Qed.

Theorem add_le_mono_l : forall n m p, n <= m <-> p + n <= p + m.
Proof.
  intros n m p; nzinduct p. - now nzsimpl.
  - intro p. nzsimpl. now rewrite <- succ_le_mono.
Qed.

Theorem add_le_mono_r : forall n m p, n <= m <-> n + p <= m + p.
Proof.
intros n m p. rewrite (add_comm n p), (add_comm m p); apply add_le_mono_l.
Qed.

Theorem add_le_mono : forall n m p q, n <= m -> p <= q -> n + p <= m + q.
Proof.
intros n m p q H1 H2.
apply le_trans with (m + p);
[now apply add_le_mono_r | now apply add_le_mono_l].
Qed.

Theorem add_lt_le_mono : forall n m p q, n < m -> p <= q -> n + p < m + q.
Proof.
intros n m p q H1 H2.
apply lt_le_trans with (m + p);
[now apply add_lt_mono_r | now apply add_le_mono_l].
Qed.

Theorem add_le_lt_mono : forall n m p q, n <= m -> p < q -> n + p < m + q.
Proof.
intros n m p q H1 H2.
apply le_lt_trans with (m + p);
[now apply add_le_mono_r | now apply add_lt_mono_l].
Qed.

Theorem add_pos_pos : forall n m, 0 < n -> 0 < m -> 0 < n + m.
Proof.
intros n m H1 H2. rewrite <- (add_0_l 0). now apply add_lt_mono.
Qed.

Theorem add_pos_nonneg : forall n m, 0 < n -> 0 <= m -> 0 < n + m.
Proof.
intros n m H1 H2. rewrite <- (add_0_l 0). now apply add_lt_le_mono.
Qed.

Theorem add_nonneg_pos : forall n m, 0 <= n -> 0 < m -> 0 < n + m.
Proof.
intros n m H1 H2. rewrite <- (add_0_l 0). now apply add_le_lt_mono.
Qed.

Theorem add_nonneg_nonneg : forall n m, 0 <= n -> 0 <= m -> 0 <= n + m.
Proof.
intros n m H1 H2. rewrite <- (add_0_l 0). now apply add_le_mono.
Qed.

Theorem lt_add_pos_l : forall n m, 0 < n -> m < n + m.
Proof.
intros n m. rewrite (add_lt_mono_r 0 n m). now nzsimpl.
Qed.

Theorem lt_add_pos_r : forall n m, 0 < n -> m < m + n.
Proof.
intros; rewrite add_comm; now apply lt_add_pos_l.
Qed.

Theorem le_lt_add_lt : forall n m p q, n <= m -> p + m < q + n -> p < q.
Proof.
intros n m p q H1 H2. destruct (le_gt_cases q p); [| assumption].
contradict H2. rewrite nlt_ge. now apply add_le_mono.
Qed.

Theorem lt_le_add_lt : forall n m p q, n < m -> p + m <= q + n -> p < q.
Proof.
intros n m p q H1 H2. destruct (le_gt_cases q p); [| assumption].
contradict H2. rewrite nle_gt. now apply add_le_lt_mono.
Qed.

Theorem le_le_add_le : forall n m p q, n <= m -> p + m <= q + n -> p <= q.
Proof.
intros n m p q H1 H2. destruct (le_gt_cases p q); [assumption |].
contradict H2. rewrite nle_gt. now apply add_lt_le_mono.
Qed.

Theorem add_lt_cases : forall n m p q, n + m < p + q -> n < p \/ m < q.
Proof.
intros n m p q H;
destruct (le_gt_cases p n) as [H1 | H1]; [| now left].
destruct (le_gt_cases q m) as [H2 | H2]; [| now right].
contradict H; rewrite nlt_ge. now apply add_le_mono.
Qed.

Theorem add_le_cases : forall n m p q, n + m <= p + q -> n <= p \/ m <= q.
Proof.
intros n m p q H.
destruct (le_gt_cases n p) as [H1 | H1]. - now left.
- destruct (le_gt_cases m q) as [H2 | H2]. + now right.
  + contradict H; rewrite nle_gt. now apply add_lt_mono.
Qed.

Theorem add_neg_cases : forall n m, n + m < 0 -> n < 0 \/ m < 0.
Proof.
intros n m H; apply add_lt_cases; now nzsimpl.
Qed.

Theorem add_pos_cases : forall n m, 0 < n + m -> 0 < n \/ 0 < m.
Proof.
intros n m H; apply add_lt_cases; now nzsimpl.
Qed.

Theorem add_nonpos_cases : forall n m, n + m <= 0 -> n <= 0 \/ m <= 0.
Proof.
intros n m H; apply add_le_cases; now nzsimpl.
Qed.

Theorem add_nonneg_cases : forall n m, 0 <= n + m -> 0 <= n \/ 0 <= m.
Proof.
intros n m H; apply add_le_cases; now nzsimpl.
Qed.

(** Subtraction *)

Lemma le_exists_sub : forall n m, n<=m -> exists p, m == p+n /\ 0<=p.
Proof.
  intros n m H. apply le_ind with (4:=H). - solve_proper.
  - exists 0; nzsimpl; split; order.
  - clear m H. intros m H (p & EQ & LE). exists (S p).
    split. + nzsimpl. now f_equiv. + now apply le_le_succ_r.
Qed.

Lemma lt_exists_sub : forall n m, n<m -> exists p, m == p+n /\ 0<p.
Proof.
  intros n m I; pose proof (lt_le_incl _ _ I) as [p [E Ip]]%le_exists_sub.
  exists p; split; [exact E |].
  apply le_lteq in Ip as [Ip | Ep]; [exact Ip | exfalso].
  apply (lt_irrefl m); rewrite E at 1; rewrite <-Ep, add_0_l; exact I.
Qed.

End NZAddOrderProp.

Module Type NatIntAddOrderProp
  (Import NZ : NZOrdAxiomsSig')
  (Import NI : IsNatInt NZ)
  (Import NZA : NZAddOrderProp NZ).

Include NatIntOrderProp NZ NI NZA NZA.

Lemma Private_nat_sub_0_l : P 0 == 0 -> forall n, 0 - n == 0.
Proof.
  intros isNat; apply (Private_nat_induction isNat); [now intros x y -> | |].
  - rewrite sub_0_r; reflexivity.
  - intros n IH; rewrite sub_succ_r, IH; exact isNat.
Qed.

Lemma Private_int_sub_succ_l :
  (forall n, S (P n) == n) -> forall n m, S n - m == S (n - m).
Proof.
  intros isInt n. nzinduct m.
  - rewrite 2!sub_0_r; reflexivity.
  - intros m; rewrite 2!sub_succ_r, isInt; split; intros IH;
      [rewrite IH, pred_succ | rewrite <-IH, isInt]; reflexivity.
Qed.

Lemma sub_succ : forall n m, S n - S m == n - m.
Proof.
  destruct (Private_int_or_nat) as [isInt | isNat].
  - intros n m; rewrite Private_int_sub_succ_l, sub_succ_r, isInt
      by (exact isInt); reflexivity.
  - intros n; apply (Private_nat_induction isNat); [now intros x y -> | |].
    + rewrite sub_succ_r, 2!sub_0_r, pred_succ; reflexivity.
    + intros m IH; rewrite sub_succ_r, IH, sub_succ_r; reflexivity.
Qed.

Lemma sub_diag : forall n, n - n == 0.
Proof.
  nzinduct n; [rewrite sub_0_r | intros n; rewrite sub_succ]; reflexivity.
Qed.

Lemma add_simpl_r : forall n m, n + m - m == n.
Proof.
  intros n; nzinduct m.
  - rewrite add_0_r, sub_0_r; reflexivity.
  - intros m; rewrite add_succ_r, sub_succ; reflexivity.
Qed.

(* add_sub was in Natural, add_simpl_r in Integer *)
(* TODO: should we keep both? *)
Lemma add_sub : forall n m, n + m - m == n.
Proof. exact add_simpl_r. Qed.

Theorem add_simpl_l n m : n + m - n == m.
Proof. rewrite add_comm; exact (add_simpl_r _ _). Qed.

Theorem sub_add_distr n m p : n - (m + p) == (n - m) - p.
Proof.
  destruct Private_int_or_nat as [isInt | isNat].
  - nzinduct p; [rewrite sub_0_r, add_0_r; reflexivity |].
    intros p; rewrite add_succ_r, 2!sub_succ_r.
    symmetry; exact (Private_int_pred_inj isInt _ _).
  - revert p; apply (Private_nat_induction isNat); [now intros x y -> | |].
    + rewrite add_0_r, sub_0_r; reflexivity.
    + intros p; rewrite add_succ_r, 2!sub_succ_r; intros ->; reflexivity.
Qed.

Theorem add_add_simpl_l_l n m p : (n + m) - (n + p) == m - p.
Proof. rewrite sub_add_distr, add_simpl_l; reflexivity. Qed.

Theorem add_add_simpl_l_r n m p : (n + m) - (p + n) == m - p.
Proof. rewrite (add_comm p n), add_add_simpl_l_l; reflexivity. Qed.

Theorem add_add_simpl_r_l n m p : (n + m) - (m + p) == n - p.
Proof. rewrite (add_comm n m), add_add_simpl_l_l; reflexivity. Qed.

Theorem add_add_simpl_r_r n m p : (n + m) - (p + m) == n - p.
Proof. rewrite (add_comm p m), add_add_simpl_r_l; reflexivity. Qed.

Theorem add_sub_eq_l : forall n m p, m + p == n -> n - m == p.
Proof. intros n m p <-; exact (add_simpl_l _ _). Qed.

Theorem add_sub_eq_r : forall n m p, m + p == n -> n - p == m.
Proof. intros n m p; rewrite add_comm; exact (add_sub_eq_l _ _ _). Qed.

Lemma Private_nat_sub_0_le : P 0 == 0 -> forall n m, n - m == 0 <-> n <= m.
Proof.
  intros isNat; apply (Private_nat_induction isNat (fun n => forall m, _)).
  - intros x y H; split; intros H' n; [rewrite <-H | rewrite H]; exact (H' _).
  - intros m; rewrite (Private_nat_sub_0_l isNat); split; intros _;
      [exact (Private_nat_le_0_l isNat _) | reflexivity].
  - intros n IH m; destruct (Private_nat_zero_or_succ isNat m) as [-> | [m' ->]].
    + rewrite sub_0_r; split; intros H; exfalso.
      * apply (Private_nat_neq_succ_0 isNat n); exact H.
      * apply (Private_nat_nle_succ_0 isNat n); exact H.
    + rewrite sub_succ, <-succ_le_mono; exact (IH _).
Qed.

Lemma Private_int_add_pred_l : (forall n, S (P n) == n) ->
  forall n m, P n + m == P (n + m).
Proof.
  intros isInt n m; rewrite <-(isInt n) at 2; now rewrite add_succ_l, pred_succ.
Qed.

Lemma Private_int_sub_add :
  (forall n, S (P n) == n) -> forall m n, m - n + n == m.
Proof.
  intros isInt m n; nzinduct n.
  - rewrite sub_0_r, add_0_r; reflexivity.
  - now intros n; rewrite add_succ_r, sub_succ_r, Private_int_add_pred_l, isInt.
Qed.

Theorem lt_0_sub : forall n m, 0 < m - n <-> n < m.
Proof.
  destruct Private_int_or_nat as [isInt | isNat].
  - intros n m; rewrite (add_lt_mono_r 0 (m - n) n), add_0_l.
    rewrite (Private_int_sub_add isInt); reflexivity.
  - intros n m; rewrite <-(Private_nat_neq_0_lt_0 isNat), lt_nge; split;
      intros H1 H2%(Private_nat_sub_0_le isNat); apply H1; exact H2.
Qed.

Lemma Private_sub_add : forall n m, n <= m -> (m - n) + n == m.
Proof.
  destruct Private_int_or_nat as [isInt | isNat]. {
    intros n m _; rewrite (Private_int_sub_add isInt); reflexivity.
  }
  apply (Private_nat_induction isNat (fun n => forall m, _ -> _)).
  - now intros x y E; split; intros H m; [rewrite <-E | rewrite E]; apply H.
  - intros m _; rewrite add_0_r, sub_0_r; reflexivity.
  - intros n IH m H; destruct (Private_nat_zero_or_succ isNat m) as [E | [k E]].
    + rewrite E in H; exfalso; exact (Private_nat_nle_succ_0 isNat n H).
    + rewrite E, sub_succ, add_succ_r, IH; [reflexivity |].
      apply succ_le_mono; rewrite E in H; exact H.
Qed.

Lemma Private_sub_add_le : forall n m, n <= n - m + m.
Proof.
  destruct Private_int_or_nat as [isInt | isNat]. {
    intros n m; rewrite (Private_int_sub_add isInt); reflexivity.
  }
  intros n m; destruct (lt_ge_cases m n) as [I | I].
  - apply lt_exists_sub in I as [p [-> I]]; rewrite add_simpl_r.
    exact (le_refl _).
  - apply (Private_nat_sub_0_le isNat) in I as E; rewrite E, add_0_l; exact I.
Qed.

Theorem le_sub_le_add_r : forall n m p, n - p <= m <-> n <= m + p.
Proof.
  intros n m p; split; intros H.
  - apply (add_le_mono_r _ _ p) in H; apply le_trans with (2 := H).
    exact (Private_sub_add_le _ _).
  - destruct Private_int_or_nat as [isInt | isNat]. {
      now apply (add_le_mono_r _ _ p); rewrite (Private_int_sub_add isInt).
    }
    destruct (le_ge_cases n p) as [I | I].
    + apply (Private_nat_sub_0_le isNat) in I as ->;
        exact (Private_nat_le_0_l isNat _).
    + apply le_exists_sub in I as [k [Ek Ik]]; rewrite Ek, add_simpl_r.
      apply (add_le_mono_r _ _ p); rewrite <-Ek; exact H.
Qed.

Theorem le_sub_le_add_l : forall n m p, n - m <= p <-> n <= m + p.
Proof. intros n m p; rewrite add_comm; exact (le_sub_le_add_r _ _ _). Qed.

Theorem lt_add_lt_sub_r : forall n m p, n + p < m <-> n < m - p.
Proof.
  intros n m p; split; intros H.
  - apply (add_lt_mono_r _ _ p), lt_le_trans with (1 := H).
    exact (Private_sub_add_le _ _).
  - destruct Private_int_or_nat as [isInt | isNat].
    + apply (add_lt_mono_r _ _ p) in H.
      rewrite (Private_int_sub_add isInt) in H; exact H.
    + assert (p <= m) as I. {
        apply lt_le_incl, lt_0_sub, le_lt_trans with (2 := H).
        exact (Private_nat_le_0_l isNat _).
      }
      apply (add_lt_mono_r _ _ p) in H.
      rewrite Private_sub_add in H by (exact I); exact H.
Qed.

Theorem lt_add_lt_sub_l : forall n m p, n + p < m <-> p < m - n.
Proof. intros n m p; rewrite add_comm; exact (lt_add_lt_sub_r _ _ _). Qed.

Theorem le_lt_sub_lt : forall n m p q, n <= m -> p - n < q - m -> p < q.
Proof.
  intros n m p q I H; apply add_le_lt_mono with (1 := I) in H as H'.
  rewrite (add_comm n), (add_comm m) in H'.
  assert (q - m + m == q) as Eq. {
    destruct Private_int_or_nat as [isInt | isNat];
      [exact (Private_int_sub_add isInt _ _) |].
    apply Private_sub_add, lt_le_incl, lt_0_sub, le_lt_trans with (2 := H).
    exact (Private_nat_le_0_l isNat _).
  }
  rewrite Eq in H'; apply le_lt_trans with (2 := H').
  exact (Private_sub_add_le _ _).
Qed.

Theorem mul_pred_r : forall n m, n * (P m) == n * m - n.
Proof.
  intros n m; destruct (eq_decidable m 0) as [-> | H%Private_succ_pred].
  - destruct Private_int_or_nat as [isInt | isNat].
    + rewrite <-(isInt 0) at 2; rewrite mul_succ_r, add_sub; reflexivity.
    + rewrite isNat, mul_0_r, Private_nat_sub_0_l by (exact isNat); reflexivity.
  - rewrite <-H at 2; rewrite mul_succ_r, add_sub; reflexivity.
Qed.

Theorem mul_pred_l : forall n m, P n * m == n * m - m.
Proof. intros n m; rewrite mul_comm, mul_pred_r, mul_comm; reflexivity. Qed.

Theorem mul_sub_distr_r : forall n m p, (n - m) * p == n * p - m * p.
Proof.
  intros n m p; destruct Private_int_or_nat as [isInt | isNat].
  - nzinduct m; [| intros m'; split].
    + rewrite mul_0_l, 2!sub_0_r; reflexivity.
    + now intros H; rewrite sub_succ_r, mul_pred_l, H, mul_succ_l, sub_add_distr.
    + intros H; rewrite <-(Private_int_sub_add isInt ((n - m') * p) p).
      rewrite sub_succ_r, mul_pred_l, mul_succ_l, sub_add_distr in H.
      rewrite H, Private_int_sub_add by (exact isInt); reflexivity.
  - revert m; apply (Private_nat_induction isNat).
    + intros x y ->; reflexivity.
    + rewrite mul_0_l, 2!sub_0_r; reflexivity.
    + intros m H; rewrite sub_succ_r, mul_pred_l, mul_succ_l, sub_add_distr, H.
      reflexivity.
Qed.

Theorem mul_sub_distr_l : forall n m p, n * (m - p) == n * m - n * p.
Proof.
  intros n m p; rewrite (mul_comm n (m - p)), (mul_comm n m), (mul_comm n p).
  exact (mul_sub_distr_r _ _ _).
Qed.

End NatIntAddOrderProp.

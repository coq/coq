(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

(*i $Id$ i*)

Require Export ZMul.

Module ZOrderPropFunct (Import ZAxiomsMod : ZAxiomsSig).
Module Export ZMulPropMod := ZMulPropFunct ZAxiomsMod.
Open Local Scope IntScope.

(* Axioms *)

Theorem Zlt_wd :
  forall n1 n2 : Z, n1 == n2 -> forall m1 m2 : Z, m1 == m2 -> (n1 < m1 <-> n2 < m2).
Proof NZlt_wd.

Theorem Zle_wd :
  forall n1 n2 : Z, n1 == n2 -> forall m1 m2 : Z, m1 == m2 -> (n1 <= m1 <-> n2 <= m2).
Proof NZle_wd.

Theorem Zmin_wd :
  forall n1 n2 : Z, n1 == n2 -> forall m1 m2 : Z, m1 == m2 -> Zmin n1 m1 == Zmin n2 m2.
Proof NZmin_wd.

Theorem Zmax_wd :
  forall n1 n2 : Z, n1 == n2 -> forall m1 m2 : Z, m1 == m2 -> Zmax n1 m1 == Zmax n2 m2.
Proof NZmax_wd.

Theorem Zlt_eq_cases : forall n m : Z, n <= m <-> n < m \/ n == m.
Proof NZlt_eq_cases.

Theorem Zlt_irrefl : forall n : Z, ~ n < n.
Proof NZlt_irrefl.

Theorem Zlt_succ_r : forall n m : Z, n < S m <-> n <= m.
Proof NZlt_succ_r.

Theorem Zmin_l : forall n m : Z, n <= m -> Zmin n m == n.
Proof NZmin_l.

Theorem Zmin_r : forall n m : Z, m <= n -> Zmin n m == m.
Proof NZmin_r.

Theorem Zmax_l : forall n m : Z, m <= n -> Zmax n m == n.
Proof NZmax_l.

Theorem Zmax_r : forall n m : Z, n <= m -> Zmax n m == m.
Proof NZmax_r.

(* Renaming theorems from NZOrder.v *)

Theorem Zlt_le_incl : forall n m : Z, n < m -> n <= m.
Proof NZlt_le_incl.

Theorem Zlt_neq : forall n m : Z, n < m -> n ~= m.
Proof NZlt_neq.

Theorem Zle_neq : forall n m : Z, n < m <-> n <= m /\ n ~= m.
Proof NZle_neq.

Theorem Zle_refl : forall n : Z, n <= n.
Proof NZle_refl.

Theorem Zlt_succ_diag_r : forall n : Z, n < S n.
Proof NZlt_succ_diag_r.

Theorem Zle_succ_diag_r : forall n : Z, n <= S n.
Proof NZle_succ_diag_r.

Theorem Zlt_0_1 : 0 < 1.
Proof NZlt_0_1.

Theorem Zle_0_1 : 0 <= 1.
Proof NZle_0_1.

Theorem Zlt_lt_succ_r : forall n m : Z, n < m -> n < S m.
Proof NZlt_lt_succ_r.

Theorem Zle_le_succ_r : forall n m : Z, n <= m -> n <= S m.
Proof NZle_le_succ_r.

Theorem Zle_succ_r : forall n m : Z, n <= S m <-> n <= m \/ n == S m.
Proof NZle_succ_r.

Theorem Zneq_succ_diag_l : forall n : Z, S n ~= n.
Proof NZneq_succ_diag_l.

Theorem Zneq_succ_diag_r : forall n : Z, n ~= S n.
Proof NZneq_succ_diag_r.

Theorem Znlt_succ_diag_l : forall n : Z, ~ S n < n.
Proof NZnlt_succ_diag_l.

Theorem Znle_succ_diag_l : forall n : Z, ~ S n <= n.
Proof NZnle_succ_diag_l.

Theorem Zle_succ_l : forall n m : Z, S n <= m <-> n < m.
Proof NZle_succ_l.

Theorem Zlt_succ_l : forall n m : Z, S n < m -> n < m.
Proof NZlt_succ_l.

Theorem Zsucc_lt_mono : forall n m : Z, n < m <-> S n < S m.
Proof NZsucc_lt_mono.

Theorem Zsucc_le_mono : forall n m : Z, n <= m <-> S n <= S m.
Proof NZsucc_le_mono.

Theorem Zlt_asymm : forall n m, n < m -> ~ m < n.
Proof NZlt_asymm.

Notation Zlt_ngt := Zlt_asymm (only parsing).

Theorem Zlt_trans : forall n m p : Z, n < m -> m < p -> n < p.
Proof NZlt_trans.

Theorem Zle_trans : forall n m p : Z, n <= m -> m <= p -> n <= p.
Proof NZle_trans.

Theorem Zle_lt_trans : forall n m p : Z, n <= m -> m < p -> n < p.
Proof NZle_lt_trans.

Theorem Zlt_le_trans : forall n m p : Z, n < m -> m <= p -> n < p.
Proof NZlt_le_trans.

Theorem Zle_antisymm : forall n m : Z, n <= m -> m <= n -> n == m.
Proof NZle_antisymm.

Theorem Zlt_1_l : forall n m : Z, 0 < n -> n < m -> 1 < m.
Proof NZlt_1_l.

(** Trichotomy, decidability, and double negation elimination *)

Theorem Zlt_trichotomy : forall n m : Z,  n < m \/ n == m \/ m < n.
Proof NZlt_trichotomy.

Notation Zlt_eq_gt_cases := Zlt_trichotomy (only parsing).

Theorem Zlt_gt_cases : forall n m : Z, n ~= m <-> n < m \/ n > m.
Proof NZlt_gt_cases.

Theorem Zle_gt_cases : forall n m : Z, n <= m \/ n > m.
Proof NZle_gt_cases.

Theorem Zlt_ge_cases : forall n m : Z, n < m \/ n >= m.
Proof NZlt_ge_cases.

Theorem Zle_ge_cases : forall n m : Z, n <= m \/ n >= m.
Proof NZle_ge_cases.

(** Instances of the previous theorems for m == 0 *)

Theorem Zneg_pos_cases : forall n : Z, n ~= 0 <-> n < 0 \/ n > 0.
Proof.
intro; apply Zlt_gt_cases.
Qed.

Theorem Znonpos_pos_cases : forall n : Z, n <= 0 \/ n > 0.
Proof.
intro; apply Zle_gt_cases.
Qed.

Theorem Zneg_nonneg_cases : forall n : Z, n < 0 \/ n >= 0.
Proof.
intro; apply Zlt_ge_cases.
Qed.

Theorem Znonpos_nonneg_cases : forall n : Z, n <= 0 \/ n >= 0.
Proof.
intro; apply Zle_ge_cases.
Qed.

Theorem Zle_ngt : forall n m : Z, n <= m <-> ~ n > m.
Proof NZle_ngt.

Theorem Znlt_ge : forall n m : Z, ~ n < m <-> n >= m.
Proof NZnlt_ge.

Theorem Zlt_dec : forall n m : Z, decidable (n < m).
Proof NZlt_dec.

Theorem Zlt_dne : forall n m, ~ ~ n < m <-> n < m.
Proof NZlt_dne.

Theorem Znle_gt : forall n m : Z, ~ n <= m <-> n > m.
Proof NZnle_gt.

Theorem Zlt_nge : forall n m : Z, n < m <-> ~ n >= m.
Proof NZlt_nge.

Theorem Zle_dec : forall n m : Z, decidable (n <= m).
Proof NZle_dec.

Theorem Zle_dne : forall n m : Z, ~ ~ n <= m <-> n <= m.
Proof NZle_dne.

Theorem Znlt_succ_r : forall n m : Z, ~ m < S n <-> n < m.
Proof NZnlt_succ_r.

Theorem Zlt_exists_pred :
  forall z n : Z, z < n -> exists k : Z, n == S k /\ z <= k.
Proof NZlt_exists_pred.

Theorem Zlt_succ_iter_r :
  forall (n : nat) (m : Z), m < NZsucc_iter (Datatypes.S n) m.
Proof NZlt_succ_iter_r.

Theorem Zneq_succ_iter_l :
  forall (n : nat) (m : Z), NZsucc_iter (Datatypes.S n) m ~= m.
Proof NZneq_succ_iter_l.

(** Stronger variant of induction with assumptions n >= 0 (n < 0)
in the induction step *)

Theorem Zright_induction :
  forall A : Z -> Prop, predicate_wd Zeq A ->
    forall z : Z, A z ->
      (forall n : Z, z <= n -> A n -> A (S n)) ->
        forall n : Z, z <= n -> A n.
Proof NZright_induction.

Theorem Zleft_induction :
  forall A : Z -> Prop, predicate_wd Zeq A ->
    forall z : Z, A z ->
      (forall n : Z, n < z -> A (S n) -> A n) ->
        forall n : Z, n <= z -> A n.
Proof NZleft_induction.

Theorem Zright_induction' :
  forall A : Z -> Prop, predicate_wd Zeq A ->
    forall z : Z,
      (forall n : Z, n <= z -> A n) ->
      (forall n : Z, z <= n -> A n -> A (S n)) ->
        forall n : Z, A n.
Proof NZright_induction'.

Theorem Zleft_induction' :
  forall A : Z -> Prop, predicate_wd Zeq A ->
    forall z : Z,
    (forall n : Z, z <= n -> A n) ->
    (forall n : Z, n < z -> A (S n) -> A n) ->
      forall n : Z, A n.
Proof NZleft_induction'.

Theorem Zstrong_right_induction :
  forall A : Z -> Prop, predicate_wd Zeq A ->
    forall z : Z,
    (forall n : Z, z <= n -> (forall m : Z, z <= m -> m < n -> A m) -> A n) ->
       forall n : Z, z <= n -> A n.
Proof NZstrong_right_induction.

Theorem Zstrong_left_induction :
  forall A : Z -> Prop, predicate_wd Zeq A ->
    forall z : Z,
      (forall n : Z, n <= z -> (forall m : Z, m <= z -> S n <= m -> A m) -> A n) ->
        forall n : Z, n <= z -> A n.
Proof NZstrong_left_induction.

Theorem Zstrong_right_induction' :
  forall A : Z -> Prop, predicate_wd Zeq A ->
    forall z : Z,
      (forall n : Z, n <= z -> A n) ->
      (forall n : Z, z <= n -> (forall m : Z, z <= m -> m < n -> A m) -> A n) ->
        forall n : Z, A n.
Proof NZstrong_right_induction'.

Theorem Zstrong_left_induction' :
  forall A : Z -> Prop, predicate_wd Zeq A ->
    forall z : Z,
    (forall n : Z, z <= n -> A n) ->
    (forall n : Z, n <= z -> (forall m : Z, m <= z -> S n <= m -> A m) -> A n) ->
      forall n : Z, A n.
Proof NZstrong_left_induction'.

Theorem Zorder_induction :
  forall A : Z -> Prop, predicate_wd Zeq A ->
    forall z : Z, A z ->
    (forall n : Z, z <= n -> A n -> A (S n)) ->
    (forall n : Z, n < z -> A (S n) -> A n) ->
      forall n : Z, A n.
Proof NZorder_induction.

Theorem Zorder_induction' :
  forall A : Z -> Prop, predicate_wd Zeq A ->
    forall z : Z, A z ->
    (forall n : Z, z <= n -> A n -> A (S n)) ->
    (forall n : Z, n <= z -> A n -> A (P n)) ->
      forall n : Z, A n.
Proof NZorder_induction'.

Theorem Zorder_induction_0 :
  forall A : Z -> Prop, predicate_wd Zeq A ->
    A 0 ->
    (forall n : Z, 0 <= n -> A n -> A (S n)) ->
    (forall n : Z, n < 0 -> A (S n) -> A n) ->
      forall n : Z, A n.
Proof NZorder_induction_0.

Theorem Zorder_induction'_0 :
  forall A : Z -> Prop, predicate_wd Zeq A ->
    A 0 ->
    (forall n : Z, 0 <= n -> A n -> A (S n)) ->
    (forall n : Z, n <= 0 -> A n -> A (P n)) ->
      forall n : Z, A n.
Proof NZorder_induction'_0.

Ltac Zinduct n := induction_maker n ltac:(apply Zorder_induction_0).

(** Elimintation principle for < *)

Theorem Zlt_ind :
  forall A : Z -> Prop, predicate_wd Zeq A ->
    forall n : Z, A (S n) ->
      (forall m : Z, n < m -> A m -> A (S m)) -> forall m : Z, n < m -> A m.
Proof NZlt_ind.

(** Elimintation principle for <= *)

Theorem Zle_ind :
  forall A : Z -> Prop, predicate_wd Zeq A ->
    forall n : Z, A n ->
      (forall m : Z, n <= m -> A m -> A (S m)) -> forall m : Z, n <= m -> A m.
Proof NZle_ind.

(** Well-founded relations *)

Theorem Zlt_wf : forall z : Z, well_founded (fun n m : Z => z <= n /\ n < m).
Proof NZlt_wf.

Theorem Zgt_wf : forall z : Z, well_founded (fun n m : Z => m < n /\ n <= z).
Proof NZgt_wf.

(* Theorems that are either not valid on N or have different proofs on N and Z *)

Theorem Zlt_pred_l : forall n : Z, P n < n.
Proof.
intro n; rewrite <- (Zsucc_pred n) at 2; apply Zlt_succ_diag_r.
Qed.

Theorem Zle_pred_l : forall n : Z, P n <= n.
Proof.
intro; apply Zlt_le_incl; apply Zlt_pred_l.
Qed.

Theorem Zlt_le_pred : forall n m : Z, n < m <-> n <= P m.
Proof.
intros n m; rewrite <- (Zsucc_pred m); rewrite Zpred_succ. apply Zlt_succ_r.
Qed.

Theorem Znle_pred_r : forall n : Z, ~ n <= P n.
Proof.
intro; rewrite <- Zlt_le_pred; apply Zlt_irrefl.
Qed.

Theorem Zlt_pred_le : forall n m : Z, P n < m <-> n <= m.
Proof.
intros n m; rewrite <- (Zsucc_pred n) at 2.
symmetry; apply Zle_succ_l.
Qed.

Theorem Zlt_lt_pred : forall n m : Z, n < m -> P n < m.
Proof.
intros; apply <- Zlt_pred_le; now apply Zlt_le_incl.
Qed.

Theorem Zle_le_pred : forall n m : Z, n <= m -> P n <= m.
Proof.
intros; apply Zlt_le_incl; now apply <- Zlt_pred_le.
Qed.

Theorem Zlt_pred_lt : forall n m : Z, n < P m -> n < m.
Proof.
intros n m H; apply Zlt_trans with (P m); [assumption | apply Zlt_pred_l].
Qed.

Theorem Zle_pred_lt : forall n m : Z, n <= P m -> n <= m.
Proof.
intros; apply Zlt_le_incl; now apply <- Zlt_le_pred.
Qed.

Theorem Zpred_lt_mono : forall n m : Z, n < m <-> P n < P m.
Proof.
intros; rewrite Zlt_le_pred; symmetry; apply Zlt_pred_le.
Qed.

Theorem Zpred_le_mono : forall n m : Z, n <= m <-> P n <= P m.
Proof.
intros; rewrite <- Zlt_pred_le; now rewrite Zlt_le_pred.
Qed.

Theorem Zlt_succ_lt_pred : forall n m : Z, S n < m <-> n < P m.
Proof.
intros n m; now rewrite (Zpred_lt_mono (S n) m), Zpred_succ.
Qed.

Theorem Zle_succ_le_pred : forall n m : Z, S n <= m <-> n <= P m.
Proof.
intros n m; now rewrite (Zpred_le_mono (S n) m), Zpred_succ.
Qed.

Theorem Zlt_pred_lt_succ : forall n m : Z, P n < m <-> n < S m.
Proof.
intros; rewrite Zlt_pred_le; symmetry; apply Zlt_succ_r.
Qed.

Theorem Zle_pred_lt_succ : forall n m : Z, P n <= m <-> n <= S m.
Proof.
intros n m; now rewrite (Zpred_le_mono n (S m)), Zpred_succ.
Qed.

Theorem Zneq_pred_l : forall n : Z, P n ~= n.
Proof.
intro; apply Zlt_neq; apply Zlt_pred_l.
Qed.

Theorem Zlt_n1_r : forall n m : Z, n < m -> m < 0 -> n < -1.
Proof.
intros n m H1 H2. apply -> Zlt_le_pred in H2.
setoid_replace (P 0) with (-1) in H2. now apply NZlt_le_trans with m.
apply <- Zeq_opp_r. now rewrite Zopp_pred, Zopp_0.
Qed.

End ZOrderPropFunct.


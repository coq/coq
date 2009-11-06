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

Require Export NMul.

Module NOrderPropFunct (Import NAxiomsMod : NAxiomsSig).
Module Export NMulPropMod := NMulPropFunct NAxiomsMod.
Open Local Scope NatScope.

(* The tactics le_less, le_equal and le_elim are inherited from NZOrder.v *)

(* Axioms *)

Theorem lt_wd :
  forall n1 n2 : N, n1 == n2 -> forall m1 m2 : N, m1 == m2 -> (n1 < m1 <-> n2 < m2).
Proof NZlt_wd.

Theorem le_wd :
  forall n1 n2 : N, n1 == n2 -> forall m1 m2 : N, m1 == m2 -> (n1 <= m1 <-> n2 <= m2).
Proof NZle_wd.

Theorem min_wd :
  forall n1 n2 : N, n1 == n2 -> forall m1 m2 : N, m1 == m2 -> min n1 m1 == min n2 m2.
Proof NZmin_wd.

Theorem max_wd :
  forall n1 n2 : N, n1 == n2 -> forall m1 m2 : N, m1 == m2 -> max n1 m1 == max n2 m2.
Proof NZmax_wd.

Theorem lt_eq_cases : forall n m : N, n <= m <-> n < m \/ n == m.
Proof NZlt_eq_cases.

Theorem lt_irrefl : forall n : N, ~ n < n.
Proof NZlt_irrefl.

Theorem lt_succ_r : forall n m : N, n < S m <-> n <= m.
Proof NZlt_succ_r.

Theorem min_l : forall n m : N, n <= m -> min n m == n.
Proof NZmin_l.

Theorem min_r : forall n m : N, m <= n -> min n m == m.
Proof NZmin_r.

Theorem max_l : forall n m : N, m <= n -> max n m == n.
Proof NZmax_l.

Theorem max_r : forall n m : N, n <= m -> max n m == m.
Proof NZmax_r.

(* Renaming theorems from NZOrder.v *)

Theorem lt_le_incl : forall n m : N, n < m -> n <= m.
Proof NZlt_le_incl.

Theorem eq_le_incl : forall n m : N, n == m -> n <= m.
Proof NZeq_le_incl.

Theorem lt_neq : forall n m : N, n < m -> n ~= m.
Proof NZlt_neq.

Theorem le_neq : forall n m : N, n < m <-> n <= m /\ n ~= m.
Proof NZle_neq.

Theorem le_refl : forall n : N, n <= n.
Proof NZle_refl.

Theorem lt_succ_diag_r : forall n : N, n < S n.
Proof NZlt_succ_diag_r.

Theorem le_succ_diag_r : forall n : N, n <= S n.
Proof NZle_succ_diag_r.

Theorem lt_0_1 : 0 < 1.
Proof NZlt_0_1.

Theorem le_0_1 : 0 <= 1.
Proof NZle_0_1.

Theorem lt_lt_succ_r : forall n m : N, n < m -> n < S m.
Proof NZlt_lt_succ_r.

Theorem le_le_succ_r : forall n m : N, n <= m -> n <= S m.
Proof NZle_le_succ_r.

Theorem le_succ_r : forall n m : N, n <= S m <-> n <= m \/ n == S m.
Proof NZle_succ_r.

Theorem neq_succ_diag_l : forall n : N, S n ~= n.
Proof NZneq_succ_diag_l.

Theorem neq_succ_diag_r : forall n : N, n ~= S n.
Proof NZneq_succ_diag_r.

Theorem nlt_succ_diag_l : forall n : N, ~ S n < n.
Proof NZnlt_succ_diag_l.

Theorem nle_succ_diag_l : forall n : N, ~ S n <= n.
Proof NZnle_succ_diag_l.

Theorem le_succ_l : forall n m : N, S n <= m <-> n < m.
Proof NZle_succ_l.

Theorem lt_succ_l : forall n m : N, S n < m -> n < m.
Proof NZlt_succ_l.

Theorem succ_lt_mono : forall n m : N, n < m <-> S n < S m.
Proof NZsucc_lt_mono.

Theorem succ_le_mono : forall n m : N, n <= m <-> S n <= S m.
Proof NZsucc_le_mono.

Theorem lt_asymm : forall n m : N, n < m -> ~ m < n.
Proof NZlt_asymm.

Notation lt_ngt := lt_asymm (only parsing).

Theorem lt_trans : forall n m p : N, n < m -> m < p -> n < p.
Proof NZlt_trans.

Theorem le_trans : forall n m p : N, n <= m -> m <= p -> n <= p.
Proof NZle_trans.

Theorem le_lt_trans : forall n m p : N, n <= m -> m < p -> n < p.
Proof NZle_lt_trans.

Theorem lt_le_trans : forall n m p : N, n < m -> m <= p -> n < p.
Proof NZlt_le_trans.

Theorem le_antisymm : forall n m : N, n <= m -> m <= n -> n == m.
Proof NZle_antisymm.

(** Trichotomy, decidability, and double negation elimination *)

Theorem lt_trichotomy : forall n m : N,  n < m \/ n == m \/ m < n.
Proof NZlt_trichotomy.

Notation lt_eq_gt_cases := lt_trichotomy (only parsing).

Theorem lt_gt_cases : forall n m : N, n ~= m <-> n < m \/ n > m.
Proof NZlt_gt_cases.

Theorem le_gt_cases : forall n m : N, n <= m \/ n > m.
Proof NZle_gt_cases.

Theorem lt_ge_cases : forall n m : N, n < m \/ n >= m.
Proof NZlt_ge_cases.

Theorem le_ge_cases : forall n m : N, n <= m \/ n >= m.
Proof NZle_ge_cases.

Theorem le_ngt : forall n m : N, n <= m <-> ~ n > m.
Proof NZle_ngt.

Theorem nlt_ge : forall n m : N, ~ n < m <-> n >= m.
Proof NZnlt_ge.

Theorem lt_dec : forall n m : N, decidable (n < m).
Proof NZlt_dec.

Theorem lt_dne : forall n m : N, ~ ~ n < m <-> n < m.
Proof NZlt_dne.

Theorem nle_gt : forall n m : N, ~ n <= m <-> n > m.
Proof NZnle_gt.

Theorem lt_nge : forall n m : N, n < m <-> ~ n >= m.
Proof NZlt_nge.

Theorem le_dec : forall n m : N, decidable (n <= m).
Proof NZle_dec.

Theorem le_dne : forall n m : N, ~ ~ n <= m <-> n <= m.
Proof NZle_dne.

Theorem nlt_succ_r : forall n m : N, ~ m < S n <-> n < m.
Proof NZnlt_succ_r.

Theorem lt_exists_pred :
  forall z n : N, z < n -> exists k : N, n == S k /\ z <= k.
Proof NZlt_exists_pred.

Theorem lt_succ_iter_r :
  forall (n : nat) (m : N), m < NZsucc_iter (Datatypes.S n) m.
Proof NZlt_succ_iter_r.

Theorem neq_succ_iter_l :
  forall (n : nat) (m : N), NZsucc_iter (Datatypes.S n) m ~= m.
Proof NZneq_succ_iter_l.

(** Stronger variant of induction with assumptions n >= 0 (n < 0)
in the induction step *)

Theorem right_induction :
  forall A : N -> Prop, Proper (Neq==>iff) A ->
    forall z : N, A z ->
      (forall n : N, z <= n -> A n -> A (S n)) ->
        forall n : N, z <= n -> A n.
Proof NZright_induction.

Theorem left_induction :
  forall A : N -> Prop, Proper (Neq==>iff) A ->
    forall z : N, A z ->
      (forall n : N, n < z -> A (S n) -> A n) ->
        forall n : N, n <= z -> A n.
Proof NZleft_induction.

Theorem right_induction' :
  forall A : N -> Prop, Proper (Neq==>iff) A ->
    forall z : N,
      (forall n : N, n <= z -> A n) ->
      (forall n : N, z <= n -> A n -> A (S n)) ->
        forall n : N, A n.
Proof NZright_induction'.

Theorem left_induction' :
  forall A : N -> Prop, Proper (Neq==>iff) A ->
    forall z : N,
    (forall n : N, z <= n -> A n) ->
    (forall n : N, n < z -> A (S n) -> A n) ->
      forall n : N, A n.
Proof NZleft_induction'.

Theorem strong_right_induction :
  forall A : N -> Prop, Proper (Neq==>iff) A ->
    forall z : N,
    (forall n : N, z <= n -> (forall m : N, z <= m -> m < n -> A m) -> A n) ->
       forall n : N, z <= n -> A n.
Proof NZstrong_right_induction.

Theorem strong_left_induction :
  forall A : N -> Prop, Proper (Neq==>iff) A ->
    forall z : N,
      (forall n : N, n <= z -> (forall m : N, m <= z -> S n <= m -> A m) -> A n) ->
        forall n : N, n <= z -> A n.
Proof NZstrong_left_induction.

Theorem strong_right_induction' :
  forall A : N -> Prop, Proper (Neq==>iff) A ->
    forall z : N,
      (forall n : N, n <= z -> A n) ->
      (forall n : N, z <= n -> (forall m : N, z <= m -> m < n -> A m) -> A n) ->
        forall n : N, A n.
Proof NZstrong_right_induction'.

Theorem strong_left_induction' :
  forall A : N -> Prop, Proper (Neq==>iff) A ->
    forall z : N,
    (forall n : N, z <= n -> A n) ->
    (forall n : N, n <= z -> (forall m : N, m <= z -> S n <= m -> A m) -> A n) ->
      forall n : N, A n.
Proof NZstrong_left_induction'.

Theorem order_induction :
  forall A : N -> Prop, Proper (Neq==>iff) A ->
    forall z : N, A z ->
      (forall n : N, z <= n -> A n -> A (S n)) ->
      (forall n : N, n < z  -> A (S n) -> A n) ->
        forall n : N, A n.
Proof NZorder_induction.

Theorem order_induction' :
  forall A : N -> Prop, Proper (Neq==>iff) A ->
    forall z : N, A z ->
      (forall n : N, z <= n -> A n -> A (S n)) ->
      (forall n : N, n <= z -> A n -> A (P n)) ->
        forall n : N, A n.
Proof NZorder_induction'.

(* We don't need order_induction_0 and order_induction'_0 (see NZOrder and
ZOrder) since they boil down to regular induction *)

(** Elimintation principle for < *)

Theorem lt_ind :
  forall A : N -> Prop, Proper (Neq==>iff) A ->
    forall n : N,
      A (S n) ->
      (forall m : N, n < m -> A m -> A (S m)) ->
        forall m : N, n < m -> A m.
Proof NZlt_ind.

(** Elimintation principle for <= *)

Theorem le_ind :
  forall A : N -> Prop, Proper (Neq==>iff) A ->
    forall n : N,
      A n ->
      (forall m : N, n <= m -> A m -> A (S m)) ->
        forall m : N, n <= m -> A m.
Proof NZle_ind.

(** Well-founded relations *)

Theorem lt_wf : forall z : N, well_founded (fun n m : N => z <= n /\ n < m).
Proof NZlt_wf.

Theorem gt_wf : forall z : N, well_founded (fun n m : N => m < n /\ n <= z).
Proof NZgt_wf.

Theorem lt_wf_0 : well_founded lt.
Proof.
setoid_replace lt with (fun n m : N => 0 <= n /\ n < m).
apply lt_wf.
intros x y; split.
intro H; split; [apply le_0_l | assumption]. now intros [_ H].
Defined.

(* Theorems that are true for natural numbers but not for integers *)

(* "le_0_l : forall n : N, 0 <= n" was proved in NBase.v *)

Theorem nlt_0_r : forall n : N, ~ n < 0.
Proof.
intro n; apply -> le_ngt. apply le_0_l.
Qed.

Theorem nle_succ_0 : forall n : N, ~ (S n <= 0).
Proof.
intros n H; apply -> le_succ_l in H; false_hyp H nlt_0_r.
Qed.

Theorem le_0_r : forall n : N, n <= 0 <-> n == 0.
Proof.
intros n; split; intro H.
le_elim H; [false_hyp H nlt_0_r | assumption].
now apply eq_le_incl.
Qed.

Theorem lt_0_succ : forall n : N, 0 < S n.
Proof.
induct n; [apply lt_succ_diag_r | intros n H; now apply lt_lt_succ_r].
Qed.

Theorem neq_0_lt_0 : forall n : N, n ~= 0 <-> 0 < n.
Proof.
cases n.
split; intro H; [now elim H | intro; now apply lt_irrefl with 0].
intro n; split; intro H; [apply lt_0_succ | apply neq_succ_0].
Qed.

Theorem eq_0_gt_0_cases : forall n : N, n == 0 \/ 0 < n.
Proof.
cases n.
now left.
intro; right; apply lt_0_succ.
Qed.

Theorem zero_one : forall n : N, n == 0 \/ n == 1 \/ 1 < n.
Proof.
induct n. now left.
cases n. intros; right; now left.
intros n IH. destruct IH as [H | [H | H]].
false_hyp H neq_succ_0.
right; right. rewrite H. apply lt_succ_diag_r.
right; right. now apply lt_lt_succ_r.
Qed.

Theorem lt_1_r : forall n : N, n < 1 <-> n == 0.
Proof.
cases n.
split; intro; [reflexivity | apply lt_succ_diag_r].
intros n. rewrite <- succ_lt_mono.
split; intro H; [false_hyp H nlt_0_r | false_hyp H neq_succ_0].
Qed.

Theorem le_1_r : forall n : N, n <= 1 <-> n == 0 \/ n == 1.
Proof.
cases n.
split; intro; [now left | apply le_succ_diag_r].
intro n. rewrite <- succ_le_mono, le_0_r, succ_inj_wd.
split; [intro; now right | intros [H | H]; [false_hyp H neq_succ_0 | assumption]].
Qed.

Theorem lt_lt_0 : forall n m : N, n < m -> 0 < m.
Proof.
intros n m; induct n.
trivial.
intros n IH H. apply IH; now apply lt_succ_l.
Qed.

Theorem lt_1_l : forall n m p : N, n < m -> m < p -> 1 < p.
Proof.
intros n m p H1 H2.
apply le_lt_trans with m. apply <- le_succ_l. apply le_lt_trans with n.
apply le_0_l. assumption. assumption.
Qed.

(** Elimination principlies for < and <= for relations *)

Section RelElim.

Variable R : relation N.
Hypothesis R_wd : Proper (Neq==>Neq==>iff) R.

Theorem le_ind_rel :
   (forall m : N, R 0 m) ->
   (forall n m : N, n <= m -> R n m -> R (S n) (S m)) ->
     forall n m : N, n <= m -> R n m.
Proof.
intros Base Step; induct n.
intros; apply Base.
intros n IH m H. elim H using le_ind.
solve_predicate_wd.
apply Step; [| apply IH]; now apply eq_le_incl.
intros k H1 H2. apply -> le_succ_l in H1. apply lt_le_incl in H1. auto.
Qed.

Theorem lt_ind_rel :
   (forall m : N, R 0 (S m)) ->
   (forall n m : N, n < m -> R n m -> R (S n) (S m)) ->
   forall n m : N, n < m -> R n m.
Proof.
intros Base Step; induct n.
intros m H. apply lt_exists_pred in H; destruct H as [m' [H _]].
rewrite H; apply Base.
intros n IH m H. elim H using lt_ind.
solve_predicate_wd.
apply Step; [| apply IH]; now apply lt_succ_diag_r.
intros k H1 H2. apply lt_succ_l in H1. auto.
Qed.

End RelElim.

(** Predecessor and order *)

Theorem succ_pred_pos : forall n : N, 0 < n -> S (P n) == n.
Proof.
intros n H; apply succ_pred; intro H1; rewrite H1 in H.
false_hyp H lt_irrefl.
Qed.

Theorem le_pred_l : forall n : N, P n <= n.
Proof.
cases n.
rewrite pred_0; now apply eq_le_incl.
intros; rewrite pred_succ;  apply le_succ_diag_r.
Qed.

Theorem lt_pred_l : forall n : N, n ~= 0 -> P n < n.
Proof.
cases n.
intro H; exfalso; now apply H.
intros; rewrite pred_succ;  apply lt_succ_diag_r.
Qed.

Theorem le_le_pred : forall n m : N, n <= m -> P n <= m.
Proof.
intros n m H; apply le_trans with n. apply le_pred_l. assumption.
Qed.

Theorem lt_lt_pred : forall n m : N, n < m -> P n < m.
Proof.
intros n m H; apply le_lt_trans with n. apply le_pred_l. assumption.
Qed.

Theorem lt_le_pred : forall n m : N, n < m -> n <= P m. (* Converse is false for n == m == 0 *)
Proof.
intro n; cases m.
intro H; false_hyp H nlt_0_r.
intros m IH. rewrite pred_succ; now apply -> lt_succ_r.
Qed.

Theorem lt_pred_le : forall n m : N, P n < m -> n <= m. (* Converse is false for n == m == 0 *)
Proof.
intros n m; cases n.
rewrite pred_0; intro H; now apply lt_le_incl.
intros n IH. rewrite pred_succ in IH. now apply <- le_succ_l.
Qed.

Theorem lt_pred_lt : forall n m : N, n < P m -> n < m.
Proof.
intros n m H; apply lt_le_trans with (P m); [assumption | apply le_pred_l].
Qed.

Theorem le_pred_le : forall n m : N, n <= P m -> n <= m.
Proof.
intros n m H; apply le_trans with (P m); [assumption | apply le_pred_l].
Qed.

Theorem pred_le_mono : forall n m : N, n <= m -> P n <= P m. (* Converse is false for n == 1, m == 0 *)
Proof.
intros n m H; elim H using le_ind_rel.
solve_relation_wd.
intro; rewrite pred_0; apply le_0_l.
intros p q H1 _; now do 2 rewrite pred_succ.
Qed.

Theorem pred_lt_mono : forall n m : N, n ~= 0 -> (n < m <-> P n < P m).
Proof.
intros n m H1; split; intro H2.
assert (m ~= 0). apply <- neq_0_lt_0. now apply lt_lt_0 with n.
now rewrite <- (succ_pred n) in H2; rewrite <- (succ_pred m) in H2 ;
[apply <- succ_lt_mono | | |].
assert (m ~= 0). apply <- neq_0_lt_0. apply lt_lt_0 with (P n).
apply lt_le_trans with (P m). assumption. apply le_pred_l.
apply -> succ_lt_mono in H2. now do 2 rewrite succ_pred in H2.
Qed.

Theorem lt_succ_lt_pred : forall n m : N, S n < m <-> n < P m.
Proof.
intros n m. rewrite pred_lt_mono by apply neq_succ_0. now rewrite pred_succ.
Qed.

Theorem le_succ_le_pred : forall n m : N, S n <= m -> n <= P m. (* Converse is false for n == m == 0 *)
Proof.
intros n m H. apply lt_le_pred. now apply -> le_succ_l.
Qed.

Theorem lt_pred_lt_succ : forall n m : N, P n < m -> n < S m. (* Converse is false for n == m == 0 *)
Proof.
intros n m H. apply <- lt_succ_r. now apply lt_pred_le.
Qed.

Theorem le_pred_le_succ : forall n m : N, P n <= m <-> n <= S m.
Proof.
intros n m; cases n.
rewrite pred_0. split; intro H; apply le_0_l.
intro n. rewrite pred_succ. apply succ_le_mono.
Qed.

End NOrderPropFunct.


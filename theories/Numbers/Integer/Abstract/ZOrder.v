Require Export ZTimes.

Module ZOrderPropFunct (Import ZAxiomsMod : ZAxiomsSig).
Module Export ZTimesPropMod := ZTimesPropFunct ZAxiomsMod.
Open Local Scope NatIntScope.

(* Axioms *)

Theorem Zle_lt_or_eq : forall n m : Z, n <= m <-> n < m \/ n == m.
Proof NZle_lt_or_eq.

Theorem Zlt_irrefl : forall n : Z, ~ n < n.
Proof NZlt_irrefl.

Theorem Zlt_succ_le : forall n m : Z, n < S m <-> n <= m.
Proof NZlt_succ_le.

(* Renaming theorems from NZOrder.v *)

Theorem Zlt_le_incl : forall n m : Z, n < m -> n <= m.
Proof NZlt_le_incl.

Theorem Zlt_neq : forall n m : Z, n < m -> n ~= m.
Proof NZlt_neq.

Theorem Zlt_le_neq : forall n m : Z, n < m <-> n <= m /\ n ~= m.
Proof NZlt_le_neq.

Theorem Zle_refl : forall n : Z, n <= n.
Proof NZle_refl.

Theorem Zlt_succ_r : forall n : Z, n < S n.
Proof NZlt_succ_r.

Theorem Zle_succ_r : forall n : Z, n <= S n.
Proof NZle_succ_r.

Theorem Zlt_lt_succ : forall n m : Z, n < m -> n < S m.
Proof NZlt_lt_succ.

Theorem Zle_le_succ : forall n m : Z, n <= m -> n <= S m.
Proof NZle_le_succ.

Theorem Zle_succ_le_or_eq_succ : forall n m : Z, n <= S m <-> n <= m \/ n == S m.
Proof NZle_succ_le_or_eq_succ.

Theorem Zneq_succ_l : forall n : Z, S n ~= n.
Proof NZneq_succ_l.

Theorem Znlt_succ_l : forall n : Z, ~ S n < n.
Proof NZnlt_succ_l.

Theorem Znle_succ_l : forall n : Z, ~ S n <= n.
Proof NZnle_succ_l.

Theorem Zlt_le_succ : forall n m : Z, n < m <-> S n <= m.
Proof NZlt_le_succ.

Theorem Zlt_succ_lt : forall n m : Z, S n < m -> n < m.
Proof NZlt_succ_lt.

Theorem Zle_succ_le : forall n m : Z, S n <= m -> n <= m.
Proof NZle_succ_le.

Theorem Zsucc_lt_mono : forall n m : Z, n < m <-> S n < S m.
Proof NZsucc_lt_mono.

Theorem Zsucc_le_mono : forall n m : Z, n <= m <-> S n <= S m.
Proof NZsucc_le_mono.

Theorem Zlt_asymm : forall n m, n < m -> ~ m < n.
Proof NZlt_asymm.

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

(** Trichotomy, decidability, and double negation elimination *)

Theorem Zlt_trichotomy : forall n m : Z,  n < m \/ n == m \/ m < n.
Proof NZlt_trichotomy.

Theorem Zle_gt_cases : forall n m : Z, n <= m \/ n > m.
Proof NZle_gt_cases.

Theorem Zlt_ge_cases : forall n m : Z, n < m \/ n >= m.
Proof NZlt_ge_cases.

Theorem Zle_ngt : forall n m : Z, n <= m <-> ~ n > m.
Proof NZle_ngt.

Theorem Znlt_ge : forall n m : Z, ~ n < m <-> n >= m.
Proof NZnlt_ge.

Theorem Zlt_em : forall n m : Z, n < m \/ ~ n < m.
Proof NZlt_em.

Theorem Zlt_dne : forall n m, ~ ~ n < m <-> n < m.
Proof NZlt_dne.

Theorem Znle_gt : forall n m : Z, ~ n <= m <-> n > m.
Proof NZnle_gt.

Theorem Zlt_nge : forall n m : Z, n < m <-> ~ n >= m.
Proof NZlt_nge.

Theorem Zle_em : forall n m : Z, n <= m \/ ~ n <= m.
Proof NZle_em.

Theorem Zle_dne : forall n m : Z, ~ ~ n <= m <-> n <= m.
Proof NZle_dne.

Theorem Zlt_nlt_succ : forall n m : Z, n < m <-> ~ m < S n.
Proof NZlt_nlt_succ.

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
  forall A : Z -> Prop, predicate_wd E A ->
    forall z : Z, A z ->
      (forall n : Z, z <= n -> A n -> A (S n)) ->
        forall n : Z, z <= n -> A n.
Proof NZright_induction.

Theorem Zleft_induction :
  forall A : Z -> Prop, predicate_wd E A ->
    forall z : Z, A z ->
      (forall n : Z, n < z -> A (S n) -> A n) ->
        forall n : Z, n <= z -> A n.
Proof NZleft_induction.

Theorem Zorder_induction :
  forall A : Z -> Prop, predicate_wd E A ->
    forall z : Z, A z ->
      (forall n : Z, z <= n -> A n -> A (S n)) ->
      (forall n : Z, n < z -> A (S n) -> A n) ->
        forall n : Z, A n.
Proof NZorder_induction.

Theorem Zorder_induction' :
  forall A : Z -> Prop, predicate_wd E A ->
    forall z : Z, A z ->
      (forall n : Z, z <= n -> A n -> A (S n)) ->
      (forall n : Z, n <= z -> A n -> A (P n)) ->
        forall n : Z, A n.
Proof.
intros A A_wd z Az AS AP n; apply Zorder_induction with (z := z); try assumption.
intros m H1 H2. apply AP in H2; [| now apply -> Zlt_le_succ].
unfold predicate_wd, fun_wd in A_wd; apply -> (A_wd (P (S m)) m);
[assumption | apply Zpred_succ].
Qed.

Theorem Zright_induction' :
  forall A : Z -> Prop, predicate_wd E A ->
    forall z : Z,
      (forall n : Z, n <= z -> A n) ->
      (forall n : Z, z <= n -> A n -> A (S n)) ->
        forall n : Z, A n.
Proof NZright_induction'.

Theorem Zstrong_right_induction' :
  forall A : Z -> Prop, predicate_wd E A ->
    forall z : Z,
      (forall n : Z, n <= z -> A n) ->
      (forall n : Z, z <= n -> (forall m : Z, z <= m -> m < n -> A m) -> A n) ->
        forall n : Z, A n.
Proof NZstrong_right_induction'.

(** Elimintation principle for < *)

Theorem Zlt_ind :
  forall A : Z -> Prop, predicate_wd E A ->
    forall n : Z,
      A (S n) ->
      (forall m : Z, n < m -> A m -> A (S m)) ->
        forall m : Z, n < m -> A m.
Proof NZlt_ind.

(** Elimintation principle for <= *)

Theorem Zle_ind :
  forall A : Z -> Prop, predicate_wd E A ->
    forall n : Z,
      A n ->
      (forall m : Z, n <= m -> A m -> A (S m)) ->
        forall m : Z, n <= m -> A m.
Proof NZle_ind.

Ltac Zinduct n := induction_maker n ltac:(apply Zorder_induction with (z := 0)).

(** Theorems that are either not valid on N or have different proofs on N and Z *)

Theorem Zlt_pred_l : forall n : Z, P n < n.
Proof.
intro n; pattern n at 2; qsetoid_rewrite <- (Zsucc_pred n); apply Zlt_succ_r.
Qed.

Theorem Zle_pred_l : forall n : Z, P n <= n.
Proof.
intro; le_less; apply Zlt_pred_l.
Qed.

Theorem Zlt_le_pred : forall n m : Z, n < m <-> n <= P m.
Proof.
intros n m; rewrite <- (Zsucc_pred m); rewrite Zpred_succ. apply Zlt_succ_le.
Qed.

Theorem Znle_pred_r : forall n : Z, ~ n <= P n.
Proof.
intro; rewrite <- Zlt_le_pred; apply Zlt_irrefl.
Qed.

Theorem Zlt_pred_le : forall n m : Z, P n < m <-> n <= m.
Proof.
intros n m; pattern n at 2; qsetoid_rewrite <- (Zsucc_pred n).
apply Zlt_le_succ.
Qed.

Theorem Zlt_lt_pred : forall n m : Z, n < m -> P n < m.
Proof.
intros; apply <- Zlt_pred_le; le_less.
Qed.

Theorem Zle_le_pred : forall n m : Z, n <= m -> P n <= m.
Proof.
intros; le_less; now apply <- Zlt_pred_le.
Qed.

Theorem Zlt_pred_lt : forall n m : Z, n < P m -> n < m.
Proof.
intros n m H; apply Zlt_trans with (P m); [assumption | apply Zlt_pred_l].
Qed.

Theorem Zle_pred_lt : forall n m : Z, n <= P m -> n <= m.
Proof.
intros; le_less; now apply <- Zlt_le_pred.
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
intros; rewrite Zlt_pred_le; symmetry; apply Zlt_succ_le.
Qed.

Theorem Zle_pred_lt_succ : forall n m : Z, P n <= m <-> n <= S m.
Proof.
intros n m; now rewrite (Zpred_le_mono n (S m)), Zpred_succ.
Qed.

Theorem Zneq_pred_l : forall n : Z, P n ~= n.
Proof.
intro; apply Zlt_neq; apply Zlt_pred_l.
Qed.

End ZOrderPropFunct.


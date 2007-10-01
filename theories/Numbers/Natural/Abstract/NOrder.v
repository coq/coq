Require Export NTimes.

Module NOrderPropFunct (Import NAxiomsMod : NAxiomsSig).
Module Export NTimesPropMod := NTimesPropFunct NAxiomsMod.
Open Local Scope NatIntScope.

(* The tactics le_less, le_equal and le_elim are inherited from NZOrder.v *)

(* Axioms *)

Theorem le_lt_or_eq : forall n m : N, n <= m <-> n < m \/ n == m.
Proof NZle_lt_or_eq.

Theorem lt_irrefl : forall n : N, ~ n < n.
Proof NZlt_irrefl.

Theorem lt_succ_le : forall n m : N, n < S m <-> n <= m.
Proof NZlt_succ_le.

(* Renaming theorems from NZOrder.v *)

Theorem lt_le_incl : forall n m : N, n < m -> n <= m.
Proof NZlt_le_incl.

Theorem lt_neq : forall n m : N, n < m -> n ~= m.
Proof NZlt_neq.

Theorem le_refl : forall n : N, n <= n.
Proof NZle_refl.

Theorem lt_succ_r : forall n : N, n < S n.
Proof NZlt_succ_r.

Theorem le_succ_r : forall n : N, n <= S n.
Proof NZle_succ_r.

Theorem lt_lt_succ : forall n m : N, n < m -> n < S m.
Proof NZlt_lt_succ.

Theorem le_le_succ : forall n m : N, n <= m -> n <= S m.
Proof NZle_le_succ.

Theorem le_succ_le_or_eq_succ : forall n m : N, n <= S m <-> n <= m \/ n == S m.
Proof NZle_succ_le_or_eq_succ.

Theorem neq_succ_l : forall n : N, S n ~= n.
Proof NZneq_succ_l.

Theorem nlt_succ_l : forall n : N, ~ S n < n.
Proof NZnlt_succ_l.

Theorem nle_succ_l : forall n : N, ~ S n <= n.
Proof NZnle_succ_l.

Theorem lt_le_succ : forall n m : N, n < m <-> S n <= m.
Proof NZlt_le_succ.

Theorem lt_succ_lt : forall n m : N, S n < m -> n < m.
Proof NZlt_succ_lt.

Theorem le_succ_le : forall n m : N, S n <= m -> n <= m.
Proof NZle_succ_le.

Theorem succ_lt_mono : forall n m : N, n < m <-> S n < S m.
Proof NZsucc_lt_mono.

Theorem succ_le_mono : forall n m : N, n <= m <-> S n <= S m.
Proof NZsucc_le_mono.

Theorem lt_asymm : forall n m, n < m -> ~ m < n.
Proof NZlt_asymm.

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

Theorem le_gt_cases : forall n m : N, n <= m \/ n > m.
Proof NZle_gt_cases.

Theorem lt_ge_cases : forall n m : N, n < m \/ n >= m.
Proof NZlt_ge_cases.

Theorem le_ngt : forall n m : N, n <= m <-> ~ n > m.
Proof NZle_ngt.

Theorem nlt_ge : forall n m : N, ~ n < m <-> n >= m.
Proof NZnlt_ge.

Theorem lt_em : forall n m : N, n < m \/ ~ n < m.
Proof NZlt_em.

Theorem lt_dne : forall n m, ~ ~ n < m <-> n < m.
Proof NZlt_dne.

Theorem nle_gt : forall n m : N, ~ n <= m <-> n > m.
Proof NZnle_gt.

Theorem lt_nge : forall n m : N, n < m <-> ~ n >= m.
Proof NZlt_nge.

Theorem le_em : forall n m : N, n <= m \/ ~ n <= m.
Proof NZle_em.

Theorem le_dne : forall n m : N, ~ ~ n <= m <-> n <= m.
Proof NZle_dne.

Theorem lt_nlt_succ : forall n m : N, n < m <-> ~ m < S n.
Proof NZlt_nlt_succ.

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
  forall A : N -> Prop, predicate_wd E A ->
    forall z : N, A z ->
      (forall n : N, z <= n -> A n -> A (S n)) ->
        forall n : N, z <= n -> A n.
Proof NZright_induction.

Theorem left_induction :
  forall A : N -> Prop, predicate_wd E A ->
    forall z : N, A z ->
      (forall n : N, n < z -> A (S n) -> A n) ->
        forall n : N, n <= z -> A n.
Proof NZleft_induction.

Theorem order_induction :
  forall A : N -> Prop, predicate_wd E A ->
    forall z : N, A z ->
      (forall n : N, z <= n -> A n -> A (S n)) ->
      (forall n : N, n < z  -> A (S n) -> A n) ->
        forall n : N, A n.
Proof NZorder_induction.

Theorem right_induction' :
  forall A : N -> Prop, predicate_wd E A ->
    forall z : N,
      (forall n : N, n <= z -> A n) ->
      (forall n : N, z <= n -> A n -> A (S n)) ->
        forall n : N, A n.
Proof NZright_induction'.

Theorem strong_right_induction' :
  forall A : N -> Prop, predicate_wd E A ->
    forall z : N,
      (forall n : N, n <= z -> A n) ->
      (forall n : N, z <= n -> (forall m : N, z <= m -> m < n -> A m) -> A n) ->
        forall n : N, A n.
Proof NZstrong_right_induction'.

(** Elimintation principle for < *)

Theorem lt_ind :
  forall A : N -> Prop, predicate_wd E A ->
    forall n : N,
      A (S n) ->
      (forall m : N, n < m -> A m -> A (S m)) ->
        forall m : N, n < m -> A m.
Proof NZlt_ind.

(** Elimintation principle for <= *)

Theorem le_ind :
  forall A : N -> Prop, predicate_wd E A ->
    forall n : N,
      A n ->
      (forall m : N, n <= m -> A m -> A (S m)) ->
        forall m : N, n <= m -> A m.
Proof NZle_ind.

(** Theorems that are true for natural numbers but not for integers *)

(* "le_0_l : forall n : N, 0 <= n" was proved in NBase.v *)

Theorem nlt_0_r : forall n : N, ~ n < 0.
Proof.
intro n; apply -> le_ngt. apply le_0_l.
Qed.

Theorem nle_succ_0 : forall n, ~ (S n <= 0).
Proof.
intros n H; apply <- lt_le_succ in H; false_hyp H nlt_0_r.
Qed.

Theorem le_0_eq_0 : forall n, n <= 0 <-> n == 0.
Proof.
intros n; split; intro H.
le_elim H; [false_hyp H nlt_0_r | assumption].
le_equal.
Qed.

Theorem lt_0_succ : forall n, 0 < S n.
Proof.
induct n; [apply lt_succ_r | intros n H; now apply lt_lt_succ].
Qed.

Theorem lt_lt_0 : forall n m, n < m -> 0 < m.
Proof.
intros n m; induct n.
trivial.
intros n IH H. apply IH; now apply lt_succ_lt.
Qed.

Theorem neq_0_lt_0 : forall n, n ~= 0 <-> 0 < n.
Proof.
cases n.
split; intro H; [now elim H | intro; now apply lt_irrefl with 0].
intro n; split; intro H; [apply lt_0_succ | apply neq_succ_0].
Qed.

Lemma Acc_nonneg_lt : forall n : N,
  Acc (fun n m => 0 <= n /\ n < m) n -> Acc NZlt n.
Proof.
intros n H; induction H as [n _ H2];
constructor; intros y H; apply H2; split; [apply le_0_l | assumption].
Qed.

Theorem lt_wf : well_founded NZlt.
Proof.
unfold well_founded; intro n; apply Acc_nonneg_lt. apply NZlt_wf.
Qed.

(** Elimination principlies for < and <= for relations *)

Section RelElim.

(* FIXME: Variable R : relation N. -- does not work *)

Variable R : N -> N -> Prop.
Hypothesis R_wd : rel_wd E E R.

Add Morphism R with signature E ==> E ==> iff as R_morph2.
Proof R_wd.

Theorem le_ind_rel :
   (forall m, R 0 m) ->
   (forall n m, n <= m -> R n m -> R (S n) (S m)) ->
     forall n m, n <= m -> R n m.
Proof.
intros Base Step; induct n.
intros; apply Base.
intros n IH m H. elim H using le_ind.
solve_predicate_wd.
apply Step; [| apply IH]; now le_equal.
intros k H1 H2. apply le_succ_le in H1. auto.
Qed.

Theorem lt_ind_rel :
   (forall m, R 0 (S m)) ->
   (forall n m, n < m -> R n m -> R (S n) (S m)) ->
   forall n m, n < m -> R n m.
Proof.
intros Base Step; induct n.
intros m H. apply lt_exists_pred in H; destruct H as [m' [H _]].
rewrite H; apply Base.
intros n IH m H. elim H using lt_ind.
solve_predicate_wd.
apply Step; [| apply IH]; now apply lt_succ_r.
intros k H1 H2. apply lt_succ_lt in H1. auto.
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
rewrite pred_0; le_equal.
intros; rewrite pred_succ;  apply le_succ_r.
Qed.

Theorem lt_pred_l : forall n : N, n ~= 0 -> P n < n.
Proof.
cases n.
intro H; elimtype False; now apply H.
intros; rewrite pred_succ;  apply lt_succ_r.
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
intros m IH. rewrite pred_succ; now apply -> lt_succ_le.
Qed.

Theorem lt_pred_le : forall n m : N, P n < m -> n <= m. (* Converse is false for n == m == 0 *)
Proof.
intros n m; cases n.
rewrite pred_0; intro H; le_less.
intros n IH. rewrite pred_succ in IH. now apply -> lt_le_succ.
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
solve_rel_wd.
intro; rewrite pred_0; apply le_0_l.
intros p q H1 _; now do 2 rewrite pred_succ.
Qed.

Theorem pred_lt_mono : forall n m : N, n ~= 0 -> (n < m <-> P n < P m).
Proof.
intros n m H1; split; intro H2.
assert (m ~= 0). apply <- neq_0_lt_0. now apply lt_lt_0 with n.
now rewrite <- (succ_pred n) in H2; rewrite <- (succ_pred m) in H2;
[apply <- succ_lt_mono | | |].
assert (m ~= 0). apply <- neq_0_lt_0. apply lt_lt_0 with (P n).
apply lt_le_trans with (P m). assumption. apply le_pred_l.
apply -> succ_lt_mono in H2. now do 2 rewrite succ_pred in H2.
Qed.

Theorem lt_succ_lt_pred : forall n m : N, S n < m <-> n < P m.
Proof.
intros n m. rewrite pred_lt_mono. apply neq_succ_0. now rewrite pred_succ.
Qed.

Theorem le_succ_le_pred : forall n m : N, S n <= m -> n <= P m. (* Converse is false for n == m == 0 *)
Proof.
intros n m H. apply lt_le_pred. now apply <- lt_le_succ.
Qed.

Theorem lt_pred_lt_succ : forall n m : N, P n < m -> n < S m. (* Converse is false for n == m == 0 *)
Proof.
intros n m H. apply <- lt_succ_le. now apply lt_pred_le.
Qed.

Theorem le_pred_le_succ : forall n m : N, P n <= m <-> n <= S m.
Proof.
intros n m; cases n.
rewrite pred_0. split; intro H; apply le_0_l.
intro n. rewrite pred_succ. apply succ_le_mono.
Qed.

End NOrderPropFunct.


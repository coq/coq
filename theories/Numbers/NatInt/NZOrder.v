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

Require Import NZAxioms.
Require Import NZTimes.
Require Import Decidable.

Module NZOrderPropFunct (Import NZOrdAxiomsMod : NZOrdAxiomsSig).
Module Export NZTimesPropMod := NZTimesPropFunct NZAxiomsMod.
Open Local Scope NatIntScope.

Ltac le_elim H := rewrite NZlt_eq_cases in H; destruct H as [H | H].

Theorem NZlt_le_incl : forall n m : NZ, n < m -> n <= m.
Proof.
intros; apply <- NZlt_eq_cases; now left.
Qed.

Theorem NZeq_le_incl : forall n m : NZ, n == m -> n <= m.
Proof.
intros; apply <- NZlt_eq_cases; now right.
Qed.

Lemma NZlt_stepl : forall x y z : NZ, x < y -> x == z -> z < y.
Proof.
intros x y z H1 H2; now rewrite <- H2.
Qed.

Lemma NZlt_stepr : forall x y z : NZ, x < y -> y == z -> x < z.
Proof.
intros x y z H1 H2; now rewrite <- H2.
Qed.

Lemma NZle_stepl : forall x y z : NZ, x <= y -> x == z -> z <= y.
Proof.
intros x y z H1 H2; now rewrite <- H2.
Qed.

Lemma NZle_stepr : forall x y z : NZ, x <= y -> y == z -> x <= z.
Proof.
intros x y z H1 H2; now rewrite <- H2.
Qed.

Declare Left  Step NZlt_stepl.
Declare Right Step NZlt_stepr.
Declare Left  Step NZle_stepl.
Declare Right Step NZle_stepr.

Theorem NZlt_neq : forall n m : NZ, n < m -> n ~= m.
Proof.
intros n m H1 H2; rewrite H2 in H1; false_hyp H1 NZlt_irrefl.
Qed.

Theorem NZle_neq : forall n m : NZ, n < m <-> n <= m /\ n ~= m.
Proof.
intros n m; split; [intro H | intros [H1 H2]].
split. now apply NZlt_le_incl. now apply NZlt_neq.
le_elim H1. assumption. false_hyp H1 H2.
Qed.

Theorem NZle_refl : forall n : NZ, n <= n.
Proof.
intro; now apply NZeq_le_incl.
Qed.

Theorem NZlt_succ_diag_r : forall n : NZ, n < S n.
Proof.
intro n. rewrite NZlt_succ_r. now apply NZeq_le_incl.
Qed.

Theorem NZle_succ_diag_r : forall n : NZ, n <= S n.
Proof.
intro; apply NZlt_le_incl; apply NZlt_succ_diag_r.
Qed.

Theorem NZlt_0_1 : 0 < 1.
Proof.
apply NZlt_succ_diag_r.
Qed.

Theorem NZle_0_1 : 0 <= 1.
Proof.
apply NZle_succ_diag_r.
Qed.

Theorem NZlt_lt_succ_r : forall n m : NZ, n < m -> n < S m.
Proof.
intros. rewrite NZlt_succ_r. now apply NZlt_le_incl.
Qed.

Theorem NZle_le_succ_r : forall n m : NZ, n <= m -> n <= S m.
Proof.
intros n m H. rewrite <- NZlt_succ_r in H. now apply NZlt_le_incl.
Qed.

Theorem NZle_succ_r : forall n m : NZ, n <= S m <-> n <= m \/ n == S m.
Proof.
intros n m; rewrite NZlt_eq_cases. now rewrite NZlt_succ_r.
Qed.

(* The following theorem is a special case of neq_succ_iter_l below,
but we prove it separately *)

Theorem NZneq_succ_diag_l : forall n : NZ, S n ~= n.
Proof.
intros n H. pose proof (NZlt_succ_diag_r n) as H1. rewrite H in H1.
false_hyp H1 NZlt_irrefl.
Qed.

Theorem NZneq_succ_diag_r : forall n : NZ, n ~= S n.
Proof.
intro n; apply NZneq_symm; apply NZneq_succ_diag_l.
Qed.

Theorem NZnlt_succ_diag_l : forall n : NZ, ~ S n < n.
Proof.
intros n H; apply NZlt_lt_succ_r in H. false_hyp H NZlt_irrefl.
Qed.

Theorem NZnle_succ_diag_l : forall n : NZ, ~ S n <= n.
Proof.
intros n H; le_elim H.
false_hyp H NZnlt_succ_diag_l. false_hyp H NZneq_succ_diag_l.
Qed.

Theorem NZle_succ_l : forall n m : NZ, S n <= m <-> n < m.
Proof.
intro n; NZinduct m n.
setoid_replace (n < n) with False using relation iff by
  (apply -> neg_false; apply NZlt_irrefl).
now setoid_replace (S n <= n) with False using relation iff by
  (apply -> neg_false; apply NZnle_succ_diag_l).
intro m. rewrite NZlt_succ_r. rewrite NZle_succ_r.
rewrite NZsucc_inj_wd.
rewrite (NZlt_eq_cases n m).
rewrite or_cancel_r.
reflexivity.
intros H1 H2; rewrite H2 in H1; false_hyp H1 NZnle_succ_diag_l.
apply NZlt_neq.
Qed.

Theorem NZlt_succ_l : forall n m : NZ, S n < m -> n < m.
Proof.
intros n m H; apply -> NZle_succ_l; now apply NZlt_le_incl.
Qed.

Theorem NZsucc_lt_mono : forall n m : NZ, n < m <-> S n < S m.
Proof.
intros n m. rewrite <- NZle_succ_l. symmetry. apply NZlt_succ_r.
Qed.

Theorem NZsucc_le_mono : forall n m : NZ, n <= m <-> S n <= S m.
Proof.
intros n m. do 2 rewrite NZlt_eq_cases.
rewrite <- NZsucc_lt_mono; now rewrite NZsucc_inj_wd.
Qed.

Theorem NZlt_asymm : forall n m, n < m -> ~ m < n.
Proof.
intros n m; NZinduct n m.
intros H _; false_hyp H NZlt_irrefl.
intro n; split; intros H H1 H2.
apply NZlt_succ_l in H1. apply -> NZlt_succ_r in H2. le_elim H2.
now apply H. rewrite H2 in H1; false_hyp H1 NZlt_irrefl.
apply NZlt_lt_succ_r in H2. apply <- NZle_succ_l in H1. le_elim H1.
now apply H. rewrite H1 in H2; false_hyp H2 NZlt_irrefl.
Qed.

Theorem NZlt_trans : forall n m p : NZ, n < m -> m < p -> n < p.
Proof.
intros n m p; NZinduct p m.
intros _ H; false_hyp H NZlt_irrefl.
intro p. do 2 rewrite NZlt_succ_r.
split; intros H H1 H2.
apply NZlt_le_incl; le_elim H2; [now apply H | now rewrite H2 in H1].
assert (n <= p) as H3. apply H. assumption. now apply NZlt_le_incl.
le_elim H3. assumption. rewrite <- H3 in H2.
elimtype False; now apply (NZlt_asymm n m).
Qed.

Theorem NZle_trans : forall n m p : NZ, n <= m -> m <= p -> n <= p.
Proof.
intros n m p H1 H2; le_elim H1.
le_elim H2. apply NZlt_le_incl; now apply NZlt_trans with (m := m).
apply NZlt_le_incl; now rewrite <- H2. now rewrite H1.
Qed.

Theorem NZle_lt_trans : forall n m p : NZ, n <= m -> m < p -> n < p.
Proof.
intros n m p H1 H2; le_elim H1.
now apply NZlt_trans with (m := m). now rewrite H1.
Qed.

Theorem NZlt_le_trans : forall n m p : NZ, n < m -> m <= p -> n < p.
Proof.
intros n m p H1 H2; le_elim H2.
now apply NZlt_trans with (m := m). now rewrite <- H2.
Qed.

Theorem NZle_antisymm : forall n m : NZ, n <= m -> m <= n -> n == m.
Proof.
intros n m H1 H2; now (le_elim H1; le_elim H2);
[elimtype False; apply (NZlt_asymm n m) | | |].
Qed.

Theorem NZlt_1_l : forall n m : NZ, 0 < n -> n < m -> 1 < m.
Proof.
intros n m H1 H2. apply <- NZle_succ_l in H1. now apply NZle_lt_trans with n.
Qed.

(** Trichotomy, decidability, and double negation elimination *)

Theorem NZlt_trichotomy : forall n m : NZ,  n < m \/ n == m \/ m < n.
Proof.
intros n m; NZinduct n m.
right; now left.
intro n; rewrite NZlt_succ_r. stepr ((S n < m \/ S n == m) \/ m <= n) by tauto.
rewrite <- (NZlt_eq_cases (S n) m).
setoid_replace (n == m) with (m == n) using relation iff by now split.
stepl (n < m \/ m < n \/ m == n) by tauto. rewrite <- NZlt_eq_cases.
apply or_iff_compat_r. symmetry; apply NZle_succ_l.
Qed.

(* Decidability of equality, even though true in each finite ring, does not
have a uniform proof. Otherwise, the proof for two fixed numbers would
reduce to a normal form that will say if the numbers are equal or not,
which cannot be true in all finite rings. Therefore, we prove decidability
in the presence of order. *)

Theorem NZeq_dec : forall n m : NZ, decidable (n == m).
Proof.
intros n m; destruct (NZlt_trichotomy n m) as [H | [H | H]].
right; intro H1; rewrite H1 in H; false_hyp H NZlt_irrefl.
now left.
right; intro H1; rewrite H1 in H; false_hyp H NZlt_irrefl.
Qed.

(* DNE stands for double-negation elimination *)

Theorem NZeq_dne : forall n m, ~ ~ n == m <-> n == m.
Proof.
intros n m; split; intro H.
destruct (NZeq_dec n m) as [H1 | H1].
assumption. false_hyp H1 H.
intro H1; now apply H1.
Qed.

Theorem NZlt_gt_cases : forall n m : NZ, n ~= m <-> n < m \/ n > m.
Proof.
intros n m; split.
pose proof (NZlt_trichotomy n m); tauto.
intros H H1; destruct H as [H | H]; rewrite H1 in H; false_hyp H NZlt_irrefl.
Qed.

Theorem NZle_gt_cases : forall n m : NZ, n <= m \/ n > m.
Proof.
intros n m; destruct (NZlt_trichotomy n m) as [H | [H | H]].
left; now apply NZlt_le_incl. left; now apply NZeq_le_incl. now right.
Qed.

(* The following theorem is cleary redundant, but helps not to
remember whether one has to say le_gt_cases or lt_ge_cases *)

Theorem NZlt_ge_cases : forall n m : NZ, n < m \/ n >= m.
Proof.
intros n m; destruct (NZle_gt_cases m n); try (now left); try (now right).
Qed.

Theorem NZle_ge_cases : forall n m : NZ, n <= m \/ n >= m.
Proof.
intros n m; destruct (NZle_gt_cases n m) as [H | H].
now left. right; now apply NZlt_le_incl.
Qed.

Theorem NZle_ngt : forall n m : NZ, n <= m <-> ~ n > m.
Proof.
intros n m. split; intro H; [intro H1 |].
eapply NZle_lt_trans in H; [| eassumption ..]. false_hyp H NZlt_irrefl.
destruct (NZle_gt_cases n m) as [H1 | H1].
assumption. false_hyp H1 H.
Qed.

(* Redundant but useful *)

Theorem NZnlt_ge : forall n m : NZ, ~ n < m <-> n >= m.
Proof.
intros n m; symmetry; apply NZle_ngt.
Qed.

Theorem NZlt_dec : forall n m : NZ, decidable (n < m).
Proof.
intros n m; destruct (NZle_gt_cases m n);
[right; now apply -> NZle_ngt | now left].
Qed.

Theorem NZlt_dne : forall n m, ~ ~ n < m <-> n < m.
Proof.
intros n m; split; intro H;
[destruct (NZlt_dec n m) as [H1 | H1]; [assumption | false_hyp H1 H] |
intro H1; false_hyp H H1].
Qed.

Theorem NZnle_gt : forall n m : NZ, ~ n <= m <-> n > m.
Proof.
intros n m. rewrite NZle_ngt. apply NZlt_dne.
Qed.

(* Redundant but useful *)

Theorem NZlt_nge : forall n m : NZ, n < m <-> ~ n >= m.
Proof.
intros n m; symmetry; apply NZnle_gt.
Qed.

Theorem NZle_dec : forall n m : NZ, decidable (n <= m).
Proof.
intros n m; destruct (NZle_gt_cases n m);
[now left | right; now apply <- NZnle_gt].
Qed.

Theorem NZle_dne : forall n m : NZ, ~ ~ n <= m <-> n <= m.
Proof.
intros n m; split; intro H;
[destruct (NZle_dec n m) as [H1 | H1]; [assumption | false_hyp H1 H] |
intro H1; false_hyp H H1].
Qed.

Theorem NZnlt_succ_r : forall n m : NZ, ~ m < S n <-> n < m.
Proof.
intros n m; rewrite NZlt_succ_r; apply NZnle_gt.
Qed.

(* The difference between integers and natural numbers is that for
every integer there is a predecessor, which is not true for natural
numbers. However, for both classes, every number that is bigger than
some other number has a predecessor. The proof of this fact by regular
induction does not go through, so we need to use strong
(course-of-value) induction. *)

Lemma NZlt_exists_pred_strong :
  forall z n m : NZ, z < m -> m <= n -> exists k : NZ, m == S k /\ z <= k.
Proof.
intro z; NZinduct n z.
intros m H1 H2; apply <- NZnle_gt in H1; false_hyp H2 H1.
intro n; split; intros IH m H1 H2.
apply -> NZle_succ_r in H2; destruct H2 as [H2 | H2].
now apply IH. exists n. now split; [| rewrite <- NZlt_succ_r; rewrite <- H2].
apply IH. assumption. now apply NZle_le_succ_r.
Qed.

Theorem NZlt_exists_pred :
  forall z n : NZ, z < n -> exists k : NZ, n == S k /\ z <= k.
Proof.
intros z n H; apply NZlt_exists_pred_strong with (z := z) (n := n).
assumption. apply NZle_refl.
Qed.

(** A corollary of having an order is that NZ is infinite *)

(* This section about infinity of NZ relies on the type nat and can be
safely removed *)

Definition NZsucc_iter (n : nat) (m : NZ) :=
  nat_rec (fun _ => NZ) m (fun _ l => S l) n.

Theorem NZlt_succ_iter_r :
  forall (n : nat) (m : NZ), m < NZsucc_iter (Datatypes.S n) m.
Proof.
intros n m; induction n as [| n IH]; simpl in *.
apply NZlt_succ_diag_r. now apply NZlt_lt_succ_r.
Qed.

Theorem NZneq_succ_iter_l :
  forall (n : nat) (m : NZ), NZsucc_iter (Datatypes.S n) m ~= m.
Proof.
intros n m H. pose proof (NZlt_succ_iter_r n m) as H1. rewrite H in H1.
false_hyp H1 NZlt_irrefl.
Qed.

(* End of the section about the infinity of NZ *)

(** Stronger variant of induction with assumptions n >= 0 (n < 0)
in the induction step *)

Section Induction.

Variable A : NZ -> Prop.
Hypothesis A_wd : predicate_wd NZeq A.

Add Morphism A with signature NZeq ==> iff as A_morph.
Proof. apply A_wd. Qed.

Section Center.

Variable z : NZ. (* A z is the basis of induction *)

Section RightInduction.

Let A' (n : NZ) := forall m : NZ, z <= m -> m < n -> A m.
Let right_step :=   forall n : NZ, z <= n -> A n -> A (S n).
Let right_step' :=  forall n : NZ, z <= n -> A' n -> A n.
Let right_step'' := forall n : NZ, A' n <-> A' (S n).

Lemma NZrs_rs' :  A z -> right_step -> right_step'.
Proof.
intros Az RS n H1 H2.
le_elim H1. apply NZlt_exists_pred in H1. destruct H1 as [k [H3 H4]].
rewrite H3. apply RS; [assumption | apply H2; [assumption | rewrite H3; apply NZlt_succ_diag_r]].
rewrite <- H1; apply Az.
Qed.

Lemma NZrs'_rs'' : right_step' -> right_step''.
Proof.
intros RS' n; split; intros H1 m H2 H3.
apply -> NZlt_succ_r in H3; le_elim H3;
[now apply H1 | rewrite H3 in *; now apply RS'].
apply H1; [assumption | now apply NZlt_lt_succ_r].
Qed.

Lemma NZrbase : A' z.
Proof.
intros m H1 H2. apply -> NZle_ngt in H1. false_hyp H2 H1.
Qed.

Lemma NZA'A_right : (forall n : NZ, A' n) -> forall n : NZ, z <= n -> A n.
Proof.
intros H1 n H2. apply H1 with (n := S n); [assumption | apply NZlt_succ_diag_r].
Qed.

Theorem NZstrong_right_induction: right_step' -> forall n : NZ, z <= n -> A n.
Proof.
intro RS'; apply NZA'A_right; unfold A'; NZinduct n z;
[apply NZrbase | apply NZrs'_rs''; apply RS'].
Qed.

Theorem NZright_induction : A z -> right_step -> forall n : NZ, z <= n -> A n.
Proof.
intros Az RS; apply NZstrong_right_induction; now apply NZrs_rs'.
Qed.

Theorem NZright_induction' :
  (forall n : NZ, n <= z -> A n) -> right_step -> forall n : NZ, A n.
Proof.
intros L R n.
destruct (NZlt_trichotomy n z) as [H | [H | H]].
apply L; now apply NZlt_le_incl.
apply L; now apply NZeq_le_incl.
apply NZright_induction. apply L; now apply NZeq_le_incl. assumption. now apply NZlt_le_incl.
Qed.

Theorem NZstrong_right_induction' :
  (forall n : NZ, n <= z -> A n) -> right_step' -> forall n : NZ, A n.
Proof.
intros L R n.
destruct (NZlt_trichotomy n z) as [H | [H | H]].
apply L; now apply NZlt_le_incl.
apply L; now apply NZeq_le_incl.
apply NZstrong_right_induction. assumption. now apply NZlt_le_incl.
Qed.

End RightInduction.

Section LeftInduction.

Let A' (n : NZ) := forall m : NZ, m <= z -> n <= m -> A m.
Let left_step :=   forall n : NZ, n < z -> A (S n) -> A n.
Let left_step' :=  forall n : NZ, n <= z -> A' (S n) -> A n.
Let left_step'' := forall n : NZ, A' n <-> A' (S n).

Lemma NZls_ls' :  A z -> left_step -> left_step'.
Proof.
intros Az LS n H1 H2. le_elim H1.
apply LS; [assumption | apply H2; [now apply <- NZle_succ_l | now apply NZeq_le_incl]].
rewrite H1; apply Az.
Qed.

Lemma NZls'_ls'' : left_step' -> left_step''.
Proof.
intros LS' n; split; intros H1 m H2 H3.
apply -> NZle_succ_l in H3. apply NZlt_le_incl in H3. now apply H1.
le_elim H3.
apply <- NZle_succ_l in H3. now apply H1.
rewrite <- H3 in *; now apply LS'.
Qed.

Lemma NZlbase : A' (S z).
Proof.
intros m H1 H2. apply -> NZle_succ_l in H2.
apply -> NZle_ngt in H1. false_hyp H2 H1.
Qed.

Lemma NZA'A_left : (forall n : NZ, A' n) -> forall n : NZ, n <= z -> A n.
Proof.
intros H1 n H2. apply H1 with (n := n); [assumption | now apply NZeq_le_incl].
Qed.

Theorem NZstrong_left_induction: left_step' -> forall n : NZ, n <= z -> A n.
Proof.
intro LS'; apply NZA'A_left; unfold A'; NZinduct n (S z);
[apply NZlbase | apply NZls'_ls''; apply LS'].
Qed.

Theorem NZleft_induction : A z -> left_step -> forall n : NZ, n <= z -> A n.
Proof.
intros Az LS; apply NZstrong_left_induction; now apply NZls_ls'.
Qed.

Theorem NZleft_induction' :
  (forall n : NZ, z <= n -> A n) -> left_step -> forall n : NZ, A n.
Proof.
intros R L n.
destruct (NZlt_trichotomy n z) as [H | [H | H]].
apply NZleft_induction. apply R. now apply NZeq_le_incl. assumption. now apply NZlt_le_incl.
rewrite H; apply R; now apply NZeq_le_incl.
apply R; now apply NZlt_le_incl.
Qed.

Theorem NZstrong_left_induction' :
  (forall n : NZ, z <= n -> A n) -> left_step' -> forall n : NZ, A n.
Proof.
intros R L n.
destruct (NZlt_trichotomy n z) as [H | [H | H]].
apply NZstrong_left_induction; auto. now apply NZlt_le_incl.
rewrite H; apply R; now apply NZeq_le_incl.
apply R; now apply NZlt_le_incl.
Qed.

End LeftInduction.

Theorem NZorder_induction :
  A z ->
  (forall n : NZ, z <= n -> A n -> A (S n)) ->
  (forall n : NZ, n < z  -> A (S n) -> A n) ->
    forall n : NZ, A n.
Proof.
intros Az RS LS n.
destruct (NZlt_trichotomy n z) as [H | [H | H]].
now apply NZleft_induction; [| | apply NZlt_le_incl].
now rewrite H.
now apply NZright_induction; [| | apply NZlt_le_incl].
Qed.

Theorem NZorder_induction' :
  A z ->
  (forall n : NZ, z <= n -> A n -> A (S n)) ->
  (forall n : NZ, n <= z -> A n -> A (P n)) ->
    forall n : NZ, A n.
Proof.
intros Az AS AP n; apply NZorder_induction; try assumption.
intros m H1 H2. apply AP in H2; [| now apply <- NZle_succ_l].
unfold predicate_wd, fun_wd in A_wd; apply -> (A_wd (P (S m)) m);
[assumption | apply NZpred_succ].
Qed.

End Center.

Theorem NZorder_induction_0 :
  A 0 ->
  (forall n : NZ, 0 <= n -> A n -> A (S n)) ->
  (forall n : NZ, n < 0  -> A (S n) -> A n) ->
    forall n : NZ, A n.
Proof (NZorder_induction 0).

Theorem NZorder_induction'_0 :
  A 0 ->
  (forall n : NZ, 0 <= n -> A n -> A (S n)) ->
  (forall n : NZ, n <= 0 -> A n -> A (P n)) ->
    forall n : NZ, A n.
Proof (NZorder_induction' 0).

(** Elimintation principle for < *)

Theorem NZlt_ind : forall (n : NZ),
  A (S n) ->
  (forall m : NZ, n < m -> A m -> A (S m)) ->
   forall m : NZ, n < m -> A m.
Proof.
intros n H1 H2 m H3.
apply NZright_induction with (S n); [assumption | | now apply <- NZle_succ_l].
intros; apply H2; try assumption. now apply -> NZle_succ_l.
Qed.

(** Elimintation principle for <= *)

Theorem NZle_ind : forall (n : NZ),
  A n ->
  (forall m : NZ, n <= m -> A m -> A (S m)) ->
   forall m : NZ, n <= m -> A m.
Proof.
intros n H1 H2 m H3.
now apply NZright_induction with n.
Qed.

End Induction.

Tactic Notation "NZord_induct" ident(n) :=
  induction_maker n ltac:(apply NZorder_induction_0).

Tactic Notation "NZord_induct" ident(n) constr(z) :=
  induction_maker n ltac:(apply NZorder_induction with z).

Section WF.

Variable z : NZ.

Let Rlt (n m : NZ) := z <= n /\ n < m.
Let Rgt (n m : NZ) := m < n /\ n <= z.

Add Morphism Rlt with signature NZeq ==> NZeq ==> iff as Rlt_wd.
Proof.
intros x1 x2 H1 x3 x4 H2; unfold Rlt; rewrite H1; now rewrite H2.
Qed.

Add Morphism Rgt with signature NZeq ==> NZeq ==> iff as Rgt_wd.
Proof.
intros x1 x2 H1 x3 x4 H2; unfold Rgt; rewrite H1; now rewrite H2.
Qed.

Lemma NZAcc_lt_wd : predicate_wd NZeq (Acc Rlt).
Proof.
unfold predicate_wd, fun_wd.
intros x1 x2 H; split; intro H1; destruct H1 as [H2];
constructor; intros; apply H2; now (rewrite H || rewrite <- H).
Qed.

Lemma NZAcc_gt_wd : predicate_wd NZeq (Acc Rgt).
Proof.
unfold predicate_wd, fun_wd.
intros x1 x2 H; split; intro H1; destruct H1 as [H2];
constructor; intros; apply H2; now (rewrite H || rewrite <- H).
Qed.

Theorem NZlt_wf : well_founded Rlt.
Proof.
unfold well_founded.
apply NZstrong_right_induction' with (z := z).
apply NZAcc_lt_wd.
intros n H; constructor; intros y [H1 H2].
apply <- NZnle_gt in H2. elim H2. now apply NZle_trans with z.
intros n H1 H2; constructor; intros m [H3 H4]. now apply H2.
Qed.

Theorem NZgt_wf : well_founded Rgt.
Proof.
unfold well_founded.
apply NZstrong_left_induction' with (z := z).
apply NZAcc_gt_wd.
intros n H; constructor; intros y [H1 H2].
apply <- NZnle_gt in H2. elim H2. now apply NZle_lt_trans with n.
intros n H1 H2; constructor; intros m [H3 H4].
apply H2. assumption. now apply <- NZle_succ_l.
Qed.

End WF.

End NZOrderPropFunct.


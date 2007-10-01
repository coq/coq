Require Import NZAxioms.
Require Import NZTimes.

Module NZOrderPropFunct (Import NZOrdAxiomsMod : NZOrdAxiomsSig).
Module Export NZTimesPropMod := NZTimesPropFunct NZAxiomsMod.
Open Local Scope NatIntScope.

Ltac le_less := rewrite NZle_lt_or_eq; left; try assumption.
Ltac le_equal := rewrite NZle_lt_or_eq; right; try reflexivity; try assumption.
Ltac le_elim H := rewrite NZle_lt_or_eq in H; destruct H as [H | H].

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

Theorem NZlt_le_incl : forall n m : NZ, n < m -> n <= m.
Proof.
intros; now le_less.
Qed.

Theorem NZlt_neq : forall n m : NZ, n < m -> n ~= m.
Proof.
intros n m H1 H2; rewrite H2 in H1; false_hyp H1 NZlt_irrefl.
Qed.

Theorem NZle_refl : forall n : NZ, n <= n.
Proof.
intro; now le_equal.
Qed.

Theorem NZlt_succ_r : forall n : NZ, n < S n.
Proof.
intro n. rewrite NZlt_succ_le. now le_equal.
Qed.

Theorem NZle_succ_r : forall n : NZ, n <= S n.
Proof.
intro; le_less; apply NZlt_succ_r.
Qed.

Theorem NZlt_lt_succ : forall n m : NZ, n < m -> n < S m.
Proof.
intros. rewrite NZlt_succ_le. now le_less.
Qed.

Theorem NZle_le_succ : forall n m : NZ, n <= m -> n <= S m.
Proof.
intros n m H; rewrite <- NZlt_succ_le in H; now le_less.
Qed.

Theorem NZle_succ_le_or_eq_succ : forall n m : NZ, n <= S m <-> n <= m \/ n == S m.
Proof.
intros n m; rewrite NZle_lt_or_eq. now rewrite NZlt_succ_le.
Qed.

(* The following theorem is a special case of neq_succ_iter_l below,
but we prove it independently *)

Theorem NZneq_succ_l : forall n : NZ, S n ~= n.
Proof.
intros n H. pose proof (NZlt_succ_r n) as H1. rewrite H in H1.
false_hyp H1 NZlt_irrefl.
Qed.

Theorem NZnlt_succ_l : forall n : NZ, ~ S n < n.
Proof.
intros n H; apply NZlt_lt_succ in H. false_hyp H NZlt_irrefl.
Qed.

Theorem NZnle_succ_l : forall n : NZ, ~ S n <= n.
Proof.
intros n H; le_elim H.
false_hyp H NZnlt_succ_l. false_hyp H NZneq_succ_l.
Qed.

Theorem NZlt_le_succ : forall n m : NZ, n < m <-> S n <= m.
Proof.
intro n; NZinduct m n.
rewrite_false (n < n) NZlt_irrefl. now rewrite_false (S n <= n) NZnle_succ_l.
intro m. rewrite NZlt_succ_le. rewrite NZle_succ_le_or_eq_succ.
rewrite NZsucc_inj_wd. rewrite (NZle_lt_or_eq n m).
rewrite or_cancel_r.
apply NZlt_neq.
intros H1 H2; rewrite H2 in H1; false_hyp H1 NZnle_succ_l.
reflexivity.
Qed.

Theorem NZlt_succ_lt : forall n m : NZ, S n < m -> n < m.
Proof.
intros n m H; apply <- NZlt_le_succ; now le_less.
Qed.

Theorem NZle_succ_le : forall n m : NZ, S n <= m -> n <= m.
Proof.
intros n m H; le_less; now apply <- NZlt_le_succ.
Qed.

Theorem NZsucc_lt_mono : forall n m : NZ, n < m <-> S n < S m.
Proof.
intros n m. rewrite NZlt_le_succ. symmetry. apply NZlt_succ_le.
Qed.

Theorem NZsucc_le_mono : forall n m : NZ, n <= m <-> S n <= S m.
Proof.
intros n m. do 2 rewrite NZle_lt_or_eq.
rewrite <- NZsucc_lt_mono; now rewrite NZsucc_inj_wd.
Qed.

Theorem NZlt_asymm : forall n m, n < m -> ~ m < n.
Proof.
intros n m; NZinduct n m.
intros H _; false_hyp H NZlt_irrefl.
intro n; split; intros H H1 H2.
apply NZlt_succ_lt in H1. apply -> NZlt_succ_le in H2. le_elim H2.
now apply H. rewrite H2 in H1; false_hyp H1 NZlt_irrefl.
apply NZlt_lt_succ in H2. apply -> NZlt_le_succ in H1. le_elim H1.
now apply H. rewrite H1 in H2; false_hyp H2 NZlt_irrefl.
Qed.

Theorem NZlt_trans : forall n m p : NZ, n < m -> m < p -> n < p.
Proof.
intros n m p; NZinduct p m.
intros _ H; false_hyp H NZlt_irrefl.
intro p. do 2 rewrite NZlt_succ_le.
split; intros H H1 H2.
le_less; le_elim H2; [now apply H | now rewrite H2 in H1].
assert (n <= p) as H3. apply H. assumption. now le_less.
le_elim H3. assumption. rewrite <- H3 in H2.
elimtype False; now apply (NZlt_asymm n m).
Qed.

Theorem NZle_trans : forall n m p : NZ, n <= m -> m <= p -> n <= p.
Proof.
intros n m p H1 H2; le_elim H1.
le_elim H2. le_less; now apply NZlt_trans with (m := m).
le_less; now rewrite <- H2. now rewrite H1.
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

(** Trichotomy, decidability, and double negation elimination *)

Theorem NZlt_trichotomy : forall n m : NZ,  n < m \/ n == m \/ m < n.
Proof.
intros n m; NZinduct n m.
right; now left.
intro n; rewrite NZlt_succ_le. stepr ((S n < m \/ S n == m) \/ m <= n) by tauto.
rewrite <- (NZle_lt_or_eq (S n) m).
setoid_replace (n == m) with (m == n) using relation iff by now split.
stepl (n < m \/ m < n \/ m == n) by tauto. rewrite <- NZle_lt_or_eq.
apply or_iff_compat_r. apply NZlt_le_succ.
Qed.

(* Decidability of equality, even though true in each finite ring, does not
have a uniform proof. Otherwise, the proof for two fixed numbers would
reduce to a normal form that will say if the numbers are equal or not,
which cannot be true in all finite rings. Therefore, we prove decidability
in the presence of order. *)
Theorem NZeq_em : forall n m : NZ, n == m \/ n ~= m.
Proof.
intros n m; destruct (NZlt_trichotomy n m) as [H | [H | H]].
right; intro H1; rewrite H1 in H; false_hyp H NZlt_irrefl.
now left.
right; intro H1; rewrite H1 in H; false_hyp H NZlt_irrefl.
Qed.

Theorem NZeq_dne : forall n m, ~ ~ n == m <-> n == m.
Proof.
intros n m; split; intro H.
destruct (NZeq_em n m) as [H1 | H1].
assumption. false_hyp H1 H.
intro H1; now apply H1.
Qed.

Theorem NZneq_lt_gt_cases : forall n m : NZ, n ~= m <-> n < m \/ n > m.
Proof.
intros n m; split.
pose proof (NZlt_trichotomy n m); tauto.
intros H H1; destruct H as [H | H]; rewrite H1 in H; false_hyp H NZlt_irrefl.
Qed.

Theorem NZle_gt_cases : forall n m : NZ, n <= m \/ n > m.
Proof.
intros n m; destruct (NZlt_trichotomy n m) as [H | [H | H]].
left; now le_less. left; now le_equal. now right.
Qed.

(* The following theorem is cleary redundant, but helps not to
remember whether one has to say le_gt_cases or lt_ge_cases *)
Theorem NZlt_ge_cases : forall n m : NZ, n < m \/ n >= m.
Proof.
intros n m; destruct (NZle_gt_cases m n); try (now left); try (now right).
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

Theorem NZlt_em : forall n m : NZ, n < m \/ ~ n < m.
Proof.
intros n m; destruct (NZle_gt_cases m n);
[right; now apply -> NZle_ngt | now left].
Qed.

Theorem NZlt_dne : forall n m, ~ ~ n < m <-> n < m.
Proof.
intros n m; split; intro H;
[destruct (NZlt_em n m) as [H1 | H1]; [assumption | false_hyp H1 H] |
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

Theorem NZle_em : forall n m : NZ, n <= m \/ ~ n <= m.
Proof.
intros n m; destruct (NZle_gt_cases n m);
[now left | right; now apply <- NZnle_gt].
Qed.

Theorem NZle_dne : forall n m : NZ, ~ ~ n <= m <-> n <= m.
Proof.
intros n m; split; intro H;
[destruct (NZle_em n m) as [H1 | H1]; [assumption | false_hyp H1 H] |
intro H1; false_hyp H H1].
Qed.

Theorem NZlt_nlt_succ : forall n m : NZ, n < m <-> ~ m < S n.
Proof.
intros n m; rewrite NZlt_succ_le; symmetry; apply NZnle_gt.
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
apply -> NZle_succ_le_or_eq_succ in H2; destruct H2 as [H2 | H2].
now apply IH. exists n. now split; [| rewrite <- NZlt_succ_le; rewrite <- H2].
apply IH. assumption. now apply NZle_le_succ.
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
apply NZlt_succ_r. now apply NZlt_lt_succ.
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
Hypothesis A_wd : predicate_wd NZE A.

Add Morphism A with signature NZE ==> iff as A_morph.
Proof A_wd.

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
rewrite H3. apply RS; [assumption | apply H2; [assumption | rewrite H3; apply NZlt_succ_r]].
rewrite <- H1; apply Az.
Qed.

Lemma NZrs'_rs'' : right_step' -> right_step''.
Proof.
intros RS' n; split; intros H1 m H2 H3.
apply -> NZlt_succ_le in H3; le_elim H3;
[now apply H1 | rewrite H3 in *; now apply RS'].
apply H1; [assumption | now apply NZlt_lt_succ].
Qed.

Lemma NZrbase : A' z.
Proof.
intros m H1 H2. apply -> NZle_ngt in H1. false_hyp H2 H1.
Qed.

Lemma NZA'A_right : (forall n : NZ, A' n) -> forall n : NZ, z <= n -> A n.
Proof.
intros H1 n H2. apply H1 with (n := S n); [assumption | apply NZlt_succ_r].
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

End RightInduction.

Section LeftInduction.

Let A' (n : NZ) := forall m : NZ, m <= z -> n <= m -> A m.
Let left_step :=   forall n : NZ, n < z -> A (S n) -> A n.
Let left_step' :=  forall n : NZ, n <= z -> A' (S n) -> A n.
Let left_step'' := forall n : NZ, A' n <-> A' (S n).

Lemma NZls_ls' :  A z -> left_step -> left_step'.
Proof.
intros Az LS n H1 H2. le_elim H1.
apply LS; [assumption | apply H2; [now apply -> NZlt_le_succ | now le_equal]].
rewrite H1; apply Az.
Qed.

Lemma NZls'_ls'' : left_step' -> left_step''.
Proof.
intros LS' n; split; intros H1 m H2 H3.
apply NZle_succ_le in H3. now apply H1.
le_elim H3.
apply -> NZlt_le_succ in H3. now apply H1.
rewrite <- H3 in *; now apply LS'.
Qed.

Lemma NZlbase : A' (S z).
Proof.
intros m H1 H2. apply <- NZlt_le_succ in H2.
apply -> NZle_ngt in H1. false_hyp H2 H1.
Qed.

Lemma NZA'A_left : (forall n : NZ, A' n) -> forall n : NZ, n <= z -> A n.
Proof.
intros H1 n H2. apply H1 with (n := n); [assumption | now le_equal].
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

End LeftInduction.

Theorem NZorder_induction :
  A z ->
  (forall n : NZ, z <= n -> A n -> A (S n)) ->
  (forall n : NZ, n < z  -> A (S n) -> A n) ->
    forall n : NZ, A n.
Proof.
intros Az RS LS n.
destruct (NZlt_trichotomy n z) as [H | [H | H]].
now apply NZleft_induction; [| | le_less].
now rewrite H.
now apply NZright_induction; [| | le_less].
Qed.

Theorem NZright_induction' :
  (forall n : NZ, n <= z -> A n) ->
  (forall n : NZ, z <= n -> A n -> A (S n)) ->
    forall n : NZ, A n.
Proof.
intros L R n.
destruct (NZlt_trichotomy n z) as [H | [H | H]].
apply L; now le_less.
apply L; now le_equal.
apply NZright_induction. apply L; now le_equal. assumption. now le_less.
Qed.

Theorem NZstrong_right_induction' :
  (forall n : NZ, n <= z -> A n) ->
  (forall n : NZ, z <= n -> (forall m : NZ, z <= m -> m < n -> A m) -> A n) ->
    forall n : NZ, A n.
Proof.
intros L R n.
destruct (NZlt_trichotomy n z) as [H | [H | H]].
apply L; now le_less.
apply L; now le_equal.
apply NZstrong_right_induction. assumption. now le_less.
Qed.

End Center.

Theorem NZorder_induction_0 :
  A 0 ->
  (forall n : NZ, 0 <= n -> A n -> A (S n)) ->
  (forall n : NZ, n < 0  -> A (S n) -> A n) ->
    forall n : NZ, A n.
Proof (NZorder_induction 0).

(** Elimintation principle for < *)

Theorem NZlt_ind : forall (n : NZ),
  A (S n) ->
  (forall m : NZ, n < m -> A m -> A (S m)) ->
   forall m : NZ, n < m -> A m.
Proof.
intros n H1 H2 m H3.
apply NZright_induction with (S n); [assumption | | now apply -> NZlt_le_succ].
intros; apply H2; try assumption. now apply <- NZlt_le_succ.
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

Let R (n m : NZ) := z <= n /\ n < m.

Add Morphism R with signature NZE ==> NZE ==> iff as R_wd.
Proof.
intros x1 x2 H1 x3 x4 H2; unfold R; rewrite H1; now rewrite H2.
Qed.

Lemma NZAcc_lt_wd : predicate_wd NZE (Acc R).
Proof.
unfold predicate_wd, fun_wd.
intros x1 x2 H; split; intro H1; destruct H1 as [H2];
constructor; intros; apply H2; now (rewrite H || rewrite <- H).
Qed.

Theorem NZlt_wf : well_founded R.
Proof.
unfold well_founded.
apply NZstrong_right_induction' with (z := z).
apply NZAcc_lt_wd.
intros n H; constructor; intros y [H1 H2].
apply <- NZnle_gt in H2. elim H2. now apply NZle_trans with z.
intros n H1 H2; constructor; intros m [H3 H4]. now apply H2.
Qed.

End WF.

End NZOrderPropFunct.


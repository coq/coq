Require Export NAxioms.

Module Type NOrderSignature.
Declare Module Export NatModule : NatSignature.
Open Local Scope NatScope.

Parameter Inline lt : N -> N -> bool.
Parameter Inline le : N -> N -> bool.

Notation "x < y" := (lt x y) : NatScope.
Notation "x <= y" := (le x y) : NatScope.
Notation "x > y" := (lt y x) (only parsing) : NatScope.
Notation "x >= y" := (le y x) (only parsing) : NatScope.

Add Morphism lt with signature E ==> E ==> eq_bool as lt_wd.
Add Morphism le with signature E ==> E ==> eq_bool as le_wd.

Axiom le_lt : forall x y, x <= y <-> x < y \/ x == y.
Axiom lt_0 : forall x, ~ (x < 0).
Axiom lt_S : forall x y, x < S y <-> x <= y.
End NOrderSignature.

Module NOrderProperties (Import NOrderModule : NOrderSignature).
Module Export NatPropertiesModule := NatProperties NatModule.
Open Local Scope NatScope.

Ltac le_intro1 := rewrite le_lt; left.
Ltac le_intro2 := rewrite le_lt; right.
Ltac le_elim H := rewrite le_lt in H; destruct H as [H | H].

Theorem le_refl : forall n, n <= n.
Proof.
intro; now le_intro2.
Qed.

Theorem le_0_r : forall n, n <= 0 -> n == 0.
Proof.
intros n H; le_elim H; [false_hyp H lt_0 | assumption].
Qed.

Theorem lt_n_Sn : forall n, n < S n.
Proof.
intro n. apply <- lt_S. now le_intro2.
Qed.

Theorem lt_closed_S : forall n m, n < m -> n < S m.
Proof.
intros. apply <- lt_S. now le_intro1.
Qed.

Theorem lt_S_lt : forall n m, S n < m -> n < m.
Proof.
intro n; induct m.
intro H; absurd_hyp H; [apply lt_0 | assumption].
intros x IH H.
apply -> lt_S in H. le_elim H.
apply IH in H; now apply lt_closed_S.
rewrite <- H.
apply lt_closed_S; apply lt_n_Sn.
Qed.

Theorem lt_0_Sn : forall n, 0 < S n.
Proof.
induct n; [apply lt_n_Sn | intros x H; now apply lt_closed_S].
Qed.

Theorem lt_trans : forall n m p, n < m -> m < p -> n < p.
Proof.
intros n m p; induct m.
intros H1 H2; absurd_hyp H1; [ apply lt_0 | assumption].
intros x IH H1 H2.
apply -> lt_S in H1. le_elim H1.
apply IH; [assumption | apply lt_S_lt; assumption].
rewrite H1; apply lt_S_lt; assumption.
Qed.

Theorem le_trans : forall n m p, n <= m -> m <= p -> n <= p.
Proof.
intros n m p H1 H2; le_elim H1.
le_elim H2. le_intro1; now apply lt_trans with (m := m).
le_intro1; now rewrite <- H2. now rewrite H1.
Qed.

Theorem le_lt_trans : forall n m p, n <= m -> m < p -> n < p.
Proof.
intros n m p H1 H2; le_elim H1.
now apply lt_trans with (m := m). now rewrite H1.
Qed.

Theorem lt_le_trans : forall n m p, n < m -> m <= p -> n < p.
Proof.
intros n m p H1 H2; le_elim H2.
now apply lt_trans with (m := m). now rewrite <- H2.
Qed.

Theorem lt_positive : forall n m, n < m -> 0 < m.
Proof.
intros n m; induct n.
trivial.
intros x IH H.
apply lt_trans with (m := S x); [apply lt_0_Sn | apply H].
Qed.

Theorem lt_resp_S : forall n m, S n < S m <-> n < m.
Proof.
intros n m; split.
intro H; apply -> lt_S in H; le_elim H.
intros; apply lt_S_lt; assumption.
rewrite <- H; apply lt_n_Sn.
induct m.
intro H; false_hyp H lt_0.
intros x IH H.
apply -> lt_S in H; le_elim H.
apply lt_trans with (m := S x).
apply IH; assumption.
apply lt_n_Sn.
rewrite H; apply lt_n_Sn.
Qed.

Theorem le_resp_S : forall n m, S n <= S m <-> n <= m.
Proof.
intros n m; do 2 rewrite le_lt.
pose proof (S_wd n m); pose proof (S_inj n m); pose proof (lt_resp_S n m); tauto.
Qed.

Theorem lt_le_S_l : forall n m, n < m <-> S n <= m.
Proof.
intros n m; nondep_induct m.
split; intro H; [false_hyp H lt_0 |
le_elim H; [false_hyp H lt_0 | false_hyp H S_0]].
intros m; split; intro H.
apply -> lt_S in H. le_elim H; [le_intro1; now apply <- lt_resp_S | le_intro2; now apply S_wd].
le_elim H; [apply lt_trans with (m := S n); [apply lt_n_Sn | assumption] |
apply S_inj in H; rewrite H; apply lt_n_Sn].
Qed.

Theorem le_S_0 : forall n, ~ (S n <= 0).
Proof.
intros n H; apply <- lt_le_S_l in H; false_hyp H lt_0.
Qed.

Theorem le_S_l_le : forall n m, S n <= m -> n <= m.
Proof.
intros; le_intro1; now apply <- lt_le_S_l.
Qed.

Theorem lt_irr : forall n, ~ (n < n).
Proof.
induct n.
apply lt_0.
intro x; unfold not; intros H1 H2; apply H1; now apply -> lt_resp_S.
Qed.

Theorem le_antisym : forall n m, n <= m -> m <= n -> n == m.
Proof.
intros n m H1 H2; le_elim H1; le_elim H2.
elimtype False; apply lt_irr with (n := n); now apply lt_trans with (m := m).
now symmetry. assumption. assumption.
Qed.

Theorem neq_0_lt : forall n, 0 # n -> 0 < n.
Proof.
induct n.
intro H; now elim H.
intros; apply lt_0_Sn.
Qed.

Theorem lt_0_neq : forall n, 0 < n -> 0 # n.
Proof.
induct n.
intro H; absurd_hyp H; [apply lt_0 | assumption].
unfold not; intros; now apply S_0 with (n := n).
Qed.

Theorem lt_asymm : forall n m, ~ (n < m /\ m < n).
Proof.
unfold not; intros n m [H1 H2].
now apply (lt_trans n m n) in H1; [false_hyp H1 lt_irr|].
Qed.

Theorem le_0_l: forall n, 0 <= n.
Proof.
induct n; [now le_intro2 | intros; le_intro1; apply lt_0_Sn].
Qed.

Theorem lt_trichotomy : forall n m, n < m \/ n == m \/ m < n.
Proof.
intros n m; induct n.
assert (H : 0 <= m); [apply le_0_l | apply -> le_lt in H; tauto].
intros n IH. destruct IH as [H | H].
assert (H1 : S n <= m); [now apply -> lt_le_S_l | apply -> le_lt in H1; tauto].
destruct H as [H | H].
right; right; rewrite H; apply lt_n_Sn.
right; right; apply lt_trans with (m := n); [assumption | apply lt_n_Sn].
Qed.

(** The law of excluded middle for < *)
Theorem lt_em : forall n m, n < m \/ ~ n < m.
Proof.
intros n m; pose proof (lt_trichotomy n m) as H.
destruct H as [H1 | H1]; [now left |].
destruct H1 as [H2 | H2].
right; rewrite H2; apply lt_irr.
right; intro; apply (lt_asymm n m); split; assumption.
Qed.

Theorem not_lt : forall n m, ~ (n < m) <-> n >= m.
Proof.
intros n m; split; intro H.
destruct (lt_trichotomy n m) as [H1 | [H1 | H1]].
false_hyp H1 H. rewrite H1; apply le_refl. now le_intro1.
intro; now apply (le_lt_trans m n m) in H; [false_hyp H lt_irr |].
Qed.

Theorem lt_or_ge : forall n m, n < m \/ n >= m.
Proof.
intros n m; rewrite <- not_lt; apply lt_em.
Qed.

Theorem nat_total_order : forall n m, n # m -> n < m \/ m < n.
Proof.
intros n m H; destruct (lt_trichotomy n m) as [A | A]; [now left |].
now destruct A as [A | A]; [elim H | right].
Qed.

Theorem lt_exists_pred : forall n, 0 < n -> exists m, n == S m.
Proof.
induct n.
intro H; false_hyp H lt_0.
intros n IH H; now exists n.
Qed.

(** Elimination principles for < and <= *)

Section Induction1.

Variable Q : N -> Prop.
Hypothesis Q_wd : pred_wd E Q.
Variable n : N.

Add Morphism Q with signature E ==> iff as Q_morph1.
Proof Q_wd.

Theorem le_ind :
  Q n ->
  (forall m, n <= m -> Q m -> Q (S m)) ->
  forall m, n <= m -> Q m.
Proof.
intros Base Step. induct m.
intro H. apply le_0_r in H. now rewrite <- H.
intros m IH H. le_elim H.
apply -> lt_S in H. now apply Step; [| apply IH].
now rewrite <- H.
Qed.

Theorem lt_ind :
  Q (S n) ->
  (forall m, n < m -> Q m -> Q (S m)) ->
   forall m, n < m -> Q m.
Proof.
intros Base Step. induct m.
intro H; false_hyp H lt_0.
intros m IH H. apply -> lt_S in H. le_elim H.
now apply Step; [| apply IH]. now rewrite <- H.
Qed.

End Induction1.

Section Induction2.

(* Variable Q : relation N. -- does not work !!! *)
Variable Q : N -> N -> Prop.
Hypothesis Q_wd : rel_wd E Q.

Add Morphism Q with signature E ==> E ==> iff as Q_morph2.
Proof Q_wd.

Theorem le_ind_rel :
   (forall m, Q 0 m) ->
   (forall n m, n <= m -> Q n m -> Q (S n) (S m)) ->
   forall n m, n <= m -> Q n m.
Proof.
intros Base Step; induct n.
intros; apply Base.
intros n IH m; nondep_induct m.
intro H; false_hyp H le_S_0.
intros m H. apply -> le_resp_S in H. now apply Step; [| apply IH].
Qed.

Theorem lt_ind_rel :
   (forall m, Q 0 (S m)) ->
   (forall n m, n < m -> Q n m -> Q (S n) (S m)) ->
   forall n m, n < m -> Q n m.
Proof.
intros Base Step; induct n.
intros m H. apply lt_exists_pred in H; destruct H as [m' H].
rewrite H; apply Base.
intros n IH m; nondep_induct m.
intro H; false_hyp H lt_0.
intros m H. apply -> lt_resp_S in H. now apply Step; [| apply IH].
Qed.

End Induction2.

End NOrderProperties.

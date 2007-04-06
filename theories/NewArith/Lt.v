Require Export Axioms.

Module Type LtSignature.
Declare Module Export NatModule : NatSignature.

Parameter lt : N -> N -> bool.

Notation "x < y" := (lt x y).

Add Morphism lt with signature E ==> E ==> eq_bool as lt_wd.

Axiom lt_0 : forall x, ~ (x < 0).
Axiom lt_S : forall x y, x < (S y) <-> x < y \/ x == y.
End LtSignature.

Module LtProperties (Export LtModule : LtSignature).

Module Export NatPropertiesModule := NatProperties NatModule.

Theorem lt_n_Sn : forall n, n < S n.
Proof.
intro n. apply <- lt_S. now right.
Qed.

Theorem lt_closed_S : forall n m, n < m -> n < S m.
Proof.
intros. apply <- lt_S. now left.
Qed.

Theorem lt_S_lt : forall n m, S n < m -> n < m.
Proof.
intro n; induct m.
intro H; absurd_hyp H; [apply lt_0 | assumption].
intros x IH H.
apply -> lt_S in H; elim H.
intro H1; apply IH in H1; now apply lt_closed_S.
intro H1; rewrite <- H1.
apply lt_closed_S; apply lt_n_Sn.
Qed.

Theorem lt_0_Sn : forall n, 0 < S n.
Proof.
induct n; [apply lt_n_Sn | intros x H; now apply lt_closed_S].
Qed.

Theorem lt_transitive : forall n m p, n < m -> m < p -> n < p.
Proof.
intros n m p; induct m.
intros H1 H2; absurd_hyp H1; [ apply lt_0 | assumption].
intros x IH H1 H2.
apply -> lt_S in H1; elim H1.
intro H; apply IH; [assumption | apply lt_S_lt; assumption].
intro H; rewrite H; apply lt_S_lt; assumption.
Qed.

Theorem lt_positive : forall n m, n < m -> 0 < m.
Proof.
intros n m; induct n.
trivial.
intros x IH H.
apply lt_transitive with (m := S x); [apply lt_0_Sn | apply H].
Qed.

Theorem S_respects_lt : forall n m, S n < S m <-> n < m.
Proof.
intros n m; split.
intro H; apply -> lt_S in H; elim H.
intros; apply lt_S_lt; assumption.
intro H1; rewrite <- H1; apply lt_n_Sn.
induct m.
intro H; absurd_hyp H; [ apply lt_0 | assumption].
intros x IH H.
apply -> lt_S in H; elim H; intro H1.
apply lt_transitive with (m := S x).
apply IH; assumption.
apply lt_n_Sn.
rewrite H1; apply lt_n_Sn.
Qed.

Theorem lt_irreflexive : forall n, ~ (n < n).
Proof.
induct n.
apply lt_0.
intro x; unfold not; intros H1 H2; apply H1; now apply -> S_respects_lt.
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

Theorem lt_asymmetric : forall n m, ~ (n < m /\ m < n).
Proof.
unfold not; intros n m [H1 H2].
now apply (lt_transitive n m n) in H1; [false_hyp H1 lt_irreflexive|].
(*firstorder with lt_transitive lt_irreflexive.*)
Qed.

Theorem eq_0_or_lt_0: forall n, 0 == n \/ 0 < n.
Proof.
induct n; [now left | intros x; right; apply lt_0_Sn].
Qed.

Theorem lt_options : forall n m, n < m -> S n < m \/ S n == m.
Proof.
intros n m; induct m.
intro H; false_hyp H lt_0.
intros x IH H.
apply -> lt_S in H; elim H; intro H1.
apply IH in H1; elim H1; intro H2.
left; apply lt_transitive with (m := x); [assumption | apply lt_n_Sn].
rewrite H2; left; apply lt_n_Sn.
right; rewrite H1; reflexivity.
Qed.

Theorem lt_trichotomy : forall n m, n < m \/ n == m \/ m < n.
Proof.
intros n m; induct n.
assert (H : 0 == m \/ 0 < m); [apply eq_0_or_lt_0 | tauto].
intros n IH. destruct IH as [H | H].
assert (S n < m \/ S n == m); [now apply lt_options | tauto].
destruct H as [H1 | H1].
right; right; rewrite H1; apply lt_n_Sn.
right; right; apply lt_transitive with (m := n); [assumption | apply lt_n_Sn].
Qed.

Theorem lt_dichotomy : forall n m, n < m \/ ~ n < m.
Proof.
intros n m; pose proof (lt_trichotomy n m) as H.
destruct H as [H1 | H1]; [now left |].
destruct H1 as [H2 | H2].
right; rewrite H2; apply lt_irreflexive.
right; intro; apply (lt_asymmetric n m); split; assumption.
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

End LtProperties.

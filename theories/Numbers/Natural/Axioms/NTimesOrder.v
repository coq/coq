Require Export NTimes.
Require Export NPlusOrder.

Module NTimesOrderProperties (Import NTimesModule : NTimesSignature)
                          (Import NOrderModule : NOrderSignature with
                            Module NatModule := NTimesModule.NPlusModule.NatModule).
Module Export NTimesPropertiesModule :=  NTimesProperties NTimesModule.
Module Export NPlusOrderPropertiesModule :=
  NPlusOrderProperties NTimesModule.NPlusModule NOrderModule.
Open Local Scope NatScope.

Lemma mult_S_lt_compat_l : forall n m p, m < p -> S n * m < S n * p.
Proof.
intros n m p; induct n.
now do 2 rewrite mult_1_l.
intros x IH H.
rewrite times_Sn_m.
set (k := S x * m); rewrite times_Sn_m; unfold k; clear k.
apply plus_lt_compat; [assumption | apply IH; assumption].
Qed.

Lemma mult_S_lt_compat_r : forall n m p, m < p -> m * (S n) < p * (S n).
Proof.
intros n m p H.
set (k := (p * (S n))); rewrite mult_comm; unfold k; clear k.
set (k := ((S n) * m)); rewrite mult_comm; unfold k; clear k.
now apply mult_S_lt_compat_l.
Qed.

Lemma mult_lt_compat_l : forall m n p, n < m -> 0 < p -> p * n < p * m.
Proof.
intros n m p H1 H2.
apply (lt_exists_pred p) in H2.
destruct H2 as [q H]. repeat rewrite H.
now apply mult_S_lt_compat_l.
Qed.

Lemma mult_lt_compat_r : forall n m p, n < m -> 0 < p -> n * p < m * p.
Proof.
intros n m p H1 H2.
apply (lt_exists_pred p) in H2.
destruct H2 as [q H]. repeat rewrite H.
now apply mult_S_lt_compat_r.
Qed.

Lemma mult_positive : forall n m, 0 < n -> 0 < m -> 0 < n * m.
Proof.
intros n m H1 H2.
rewrite <- (times_0_n m); now apply mult_lt_compat_r.
Qed.

Lemma mult_lt_compat : forall n m p q, n < m -> p < q -> n * p < m * q.
Proof.
intros n m p q; induct n.
intros; rewrite times_0_n; apply mult_positive;
[assumption | apply lt_positive with (n := p); assumption].
intros x IH H1 H2.
apply lt_trans with (m := ((S x) * q)).
now apply mult_S_lt_compat_l; assumption.
now apply mult_lt_compat_r; [| apply lt_positive with (n := p)].
Qed.

End NTimesOrderProperties.

Require Export NTimes.
Require Export NPlusOrder.

Module NTimesOrderProperties (Import NTimesMod : NTimesSig)
                          (Import NOrderModule : NOrderSig with
                            Module NBaseMod := NTimesMod.NPlusMod.NBaseMod).
Module Export NTimesPropertiesModule :=  NTimesPropFunct NTimesMod.
Module Export NPlusOrderPropertiesModule :=
  NPlusOrderProperties NTimesMod.NPlusMod NOrderModule.
Open Local Scope NatScope.

Lemma times_succ_lt_compat_l : forall n m p, m < p -> S n * m < S n * p.
Proof.
intros n m p; induct n.
now do 2 rewrite times_1_l.
intros x IH H.
rewrite times_succ_l.
set (k := S x * m); rewrite times_succ_l; unfold k; clear k.
apply plus_lt_compat; [apply IH; assumption | assumption].
Qed.

Lemma times_succ_lt_compat_r : forall n m p, m < p -> m * (S n) < p * (S n).
Proof.
intros n m p H.
set (k := (p * (S n))); rewrite times_comm; unfold k; clear k.
set (k := ((S n) * m)); rewrite times_comm; unfold k; clear k.
now apply times_succ_lt_compat_l.
Qed.

Lemma times_lt_compat_l : forall m n p, n < m -> 0 < p -> p * n < p * m.
Proof.
intros n m p H1 H2.
apply (lt_exists_pred p) in H2.
destruct H2 as [q H]. repeat rewrite H.
now apply times_succ_lt_compat_l.
Qed.

Lemma times_lt_compat_r : forall n m p, n < m -> 0 < p -> n * p < m * p.
Proof.
intros n m p H1 H2.
apply (lt_exists_pred p) in H2.
destruct H2 as [q H]. repeat rewrite H.
now apply times_succ_lt_compat_r.
Qed.

Lemma times_positive : forall n m, 0 < n -> 0 < m -> 0 < n * m.
Proof.
intros n m H1 H2.
rewrite <- (times_0_l m); now apply times_lt_compat_r.
Qed.

Lemma times_lt_compat : forall n m p q, n < m -> p < q -> n * p < m * q.
Proof.
intros n m p q; induct n.
intros; rewrite times_0_l; apply times_positive;
[assumption | apply lt_positive with (n := p); assumption].
intros x IH H1 H2.
apply lt_trans with (m := ((S x) * q)).
now apply times_succ_lt_compat_l; assumption.
now apply times_lt_compat_r; [| apply lt_positive with (n := p)].
Qed.

End NTimesOrderProperties.


(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)

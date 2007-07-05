Require Export NPlus.
Require Export NLt.

Module PlusLtProperties (Import PlusModule : PlusSignature)
                        (Import LtModule : LtSignature with
                           Module NatModule := PlusModule.NatModule).
Module Export PlusPropertiesModule := PlusProperties PlusModule.
Module Export LtPropertiesModule := LtProperties LtModule.
Open Local Scope NScope.

(* Print All locks up here !!! *)
Theorem lt_plus_trans : forall n m p, n < m -> n < m + p.
Proof.
intros n m p; induct p.
now rewrite plus_0_r.
intros x IH H.
rewrite plus_n_Sm. apply lt_closed_S. apply IH; apply H.
Qed.

Lemma plus_lt_compat_l : forall n m p, n < m -> p + n < p + m.
Proof.
intros n m p H; induct p.
do 2 rewrite plus_0_n; assumption.
intros x IH. do 2 rewrite plus_Sn_m. now apply <- S_respects_lt.
Qed.

Lemma plus_lt_compat_r : forall n m p, n < m -> n + p < m + p.
Proof.
intros n m p H; rewrite plus_comm.
set (k := p + n); rewrite plus_comm; unfold k; clear k.
now apply plus_lt_compat_l.
Qed.

Lemma plus_lt_compat : forall n m p q, n < m -> p < q -> n + p < m + q.
Proof.
intros n m p q H1 H2.
apply lt_transitive with (m := m + p);
[now apply plus_lt_compat_r | now apply plus_lt_compat_l].
Qed.

Lemma plus_lt_reg_l : forall n m p, p + n < p + m -> n < m.
Proof.
intros n m p; induct p.
now do 2 rewrite plus_0_n.
intros x IH H.
do 2 rewrite plus_Sn_m in H.
apply IH; now apply -> S_respects_lt.
Qed.

End PlusLtProperties.

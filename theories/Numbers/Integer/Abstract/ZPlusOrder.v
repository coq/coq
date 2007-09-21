Require Export ZOrder.
Require Export ZPlus.

Module ZPlusOrderProperties (Import ZPlusModule : ZPlusSignature)
                            (Import ZOrderModule : ZOrderSignature with
                              Module ZBaseMod := ZPlusModule.ZBaseMod).
Module Export ZPlusPropertiesModule := ZPlusProperties ZPlusModule.
Module Export ZOrderPropertiesModule := ZOrderProperties ZOrderModule.
(* <W> Grammar extension: in [tactic:simple_tactic], some rule has been masked !!! *)
Open Local Scope IntScope.

Theorem plus_lt_compat_l : forall n m p, n < m <-> p + n < p + m.
Proof.
intros n m p; induct p.
now do 2 rewrite plus_0.
intros p IH. do 2 rewrite plus_succ. now rewrite <- lt_respects_succ.
intros p IH. do 2 rewrite plus_pred. now rewrite <- lt_respects_pred.
Qed.

Theorem plus_lt_compat_r : forall n m p, n < m <-> n + p < m + p.
Proof.
intros n m p; rewrite (plus_comm n p); rewrite (plus_comm m p);
apply plus_lt_compat_l.
Qed.

Theorem plus_le_compat_l : forall n m p, n <= m <-> p + n <= p + m.
Proof.
intros n m p; do 2 rewrite <- lt_succ. rewrite <- plus_n_succm;
apply plus_lt_compat_l.
Qed.

Theorem plus_le_compat_r : forall n m p, n <= m <-> n + p <= m + p.
Proof.
intros n m p; rewrite (plus_comm n p); rewrite (plus_comm m p);
apply plus_le_compat_l.
Qed.

Theorem plus_lt_compat : forall n m p q, n < m -> p < q -> n + p < m + q.
Proof.
intros n m p q H1 H2. apply lt_trans with (m := m + p).
now apply -> plus_lt_compat_r. now apply -> plus_lt_compat_l.
Qed.

Theorem plus_lt_le_compat : forall n m p q, n < m -> p <= q -> n + p < m + q.
Proof.
intros n m p q H1 H2. Zle_elim H2. now apply plus_lt_compat.
rewrite H2. now apply -> plus_lt_compat_r.
Qed.

Theorem plus_le_lt_compat : forall n m p q, n <= m -> p < q -> n + p < m + q.
Proof.
intros n m p q H1 H2. Zle_elim H1. now apply plus_lt_compat.
rewrite H1. now apply -> plus_lt_compat_l.
Qed.

Theorem plus_le_compat : forall n m p q, n <= m -> p <= q -> n + p <= m + q.
Proof.
intros n m p q H1 H2. Zle_elim H1. Zle_intro1; now apply plus_lt_le_compat.
rewrite H1. now apply -> plus_le_compat_l.
Qed.

Theorem plus_pos : forall n m, 0 <= n -> 0 <= m -> 0 <= n + m.
Proof.
intros; rewrite <- (plus_0 0); now apply plus_le_compat.
Qed.

Lemma lt_opp_forward : forall n m, n < m -> - m < - n.
Proof.
induct n.
induct_ord m.
intro H; false_hyp H lt_irr.
intros m H1 IH H2. rewrite uminus_succ. rewrite uminus_0 in *.
Zle_elim H1. apply IH in H1. now apply lt_predn_m.
rewrite <- H1; rewrite uminus_0; apply lt_predn_n.
intros m H1 IH H2. apply lt_n_predm in H2. apply -> le_gt in H1. false_hyp H2 H1.
intros n IH m H. rewrite uminus_succ.
apply -> lt_succ_pred in H. apply IH in H. rewrite uminus_pred in H. now apply -> lt_succ_pred.
intros n IH m H. rewrite uminus_pred.
apply -> lt_pred_succ in H. apply IH in H. rewrite uminus_succ in H. now apply -> lt_pred_succ.
Qed.

Theorem lt_opp : forall n m, n < m <-> - m < - n.
Proof.
intros n m; split.
apply lt_opp_forward.
intro; rewrite <- (double_opp n); rewrite <- (double_opp m);
now apply lt_opp_forward.
Qed.

Theorem le_opp : forall n m, n <= m <-> - m <= - n.
Proof.
intros n m; do 2 rewrite -> le_lt; rewrite <- lt_opp.
assert (n == m <-> - m == - n).
split; intro; [now apply uminus_wd | now apply opp_inj].
tauto.
Qed.

Theorem lt_opp_neg : forall n, n < 0 <-> 0 < - n.
Proof.
intro n. set (k := 0) in |-* at 2.
setoid_replace k with (- k); unfold k; clear k.
apply lt_opp. now rewrite uminus_0.
Qed.

Theorem le_opp_neg : forall n, n <= 0 <-> 0 <= - n.
Proof.
intro n. set (k := 0) in |-* at 2.
setoid_replace k with (- k); unfold k; clear k.
apply le_opp. now rewrite uminus_0.
Qed.

Theorem lt_opp_pos : forall n, 0 < n <-> - n < 0.
Proof.
intro n. set (k := 0) in |-* at 2.
setoid_replace k with (- k); unfold k; clear k.
apply lt_opp. now rewrite uminus_0.
Qed.

Theorem le_opp_pos : forall n, 0 <= n <-> - n <= 0.
Proof.
intro n. set (k := 0) in |-* at 2.
setoid_replace k with (- k); unfold k; clear k.
apply le_opp. now rewrite uminus_0.
Qed.

Theorem minus_lt_decr_r : forall n m p, n < m <-> p - m < p - n.
Proof.
intros n m p. do 2 rewrite <- plus_opp_minus. rewrite <- plus_lt_compat_l.
apply lt_opp.
Qed.

Theorem minus_le_nonincr_r : forall n m p, n <= m <-> p - m <= p - n.
Proof.
intros n m p. do 2 rewrite <- plus_opp_minus. rewrite <- plus_le_compat_l.
apply le_opp.
Qed.

Theorem minus_lt_incr_l : forall n m p, n < m <-> n - p < m - p.
Proof.
intros n m p. do 2 rewrite <- plus_opp_minus. now rewrite <- plus_lt_compat_r.
Qed.

Theorem minus_le_nondecr_l : forall n m p, n <= m <-> n - p <= m - p.
Proof.
intros n m p. do 2 rewrite <- plus_opp_minus. now rewrite <- plus_le_compat_r.
Qed.

Theorem lt_plus_swap : forall n m p, n + p < m <-> n < m - p.
Proof.
intros n m p. rewrite (minus_lt_incr_l (n + p) m p).
rewrite <- plus_minus_distr. rewrite minus_diag. now rewrite plus_n_0.
Qed.

Theorem le_plus_swap : forall n m p, n + p <= m <-> n <= m - p.
Proof.
intros n m p. rewrite (minus_le_nondecr_l (n + p) m p).
rewrite <- plus_minus_distr. rewrite minus_diag. now rewrite plus_n_0.
Qed.

End ZPlusOrderProperties.


(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)

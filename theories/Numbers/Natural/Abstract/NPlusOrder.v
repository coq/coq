Require Export NPlus.
Require Export NOrder.
Require Import NZPlusOrder.

Module NPlusOrderPropFunct
  (Import NPlusMod : NPlusSig)
  (Import NOrderMod : NOrderSig with Module NAxiomsMod := NPlusMod.NAxiomsMod).
Module Export NPlusPropMod := NPlusPropFunct NPlusMod.
Module Export NOrderPropMod := NOrderPropFunct NOrderMod.
Module Export NZPlusOrderPropMod := NZPlusOrderPropFunct NZPlusMod NZOrderMod.
Open Local Scope NatScope.

(* Print All locks up here !!! *)
Theorem lt_plus_trans : forall n m p, n < m -> n < m + p.
Proof.
intros n m p; induct p.
now rewrite plus_0_r.
intros x IH H.
rewrite plus_succ_r. apply lt_closed_succ. apply IH; apply H.
Qed.

Theorem plus_lt_compat_l : forall n m p, n < m -> p + n < p + m.
Proof.
intros n m p H; induct p.
do 2 rewrite plus_0_l; assumption.
intros x IH. do 2 rewrite plus_succ_l. now apply <- lt_resp_succ.
Qed.

Theorem plus_lt_compat_r : forall n m p, n < m -> n + p < m + p.
Proof.
intros n m p H; rewrite plus_comm.
set (k := p + n); rewrite plus_comm; unfold k; clear k.
now apply plus_lt_compat_l.
Qed.

Theorem plus_lt_compat : forall n m p q, n < m -> p < q -> n + p < m + q.
Proof.
intros n m p q H1 H2.
apply lt_trans with (m := m + p);
[now apply plus_lt_compat_r | now apply plus_lt_compat_l].
Qed.

Theorem plus_lt_cancel_l : forall p n m, p + n < p + m <-> n < m.
Proof.
intros p n m; induct p.
now do 2 rewrite plus_0_l.
intros p IH.
do 2 rewrite plus_succ_l. now rewrite lt_resp_succ.
Qed.

Theorem plus_lt_cancel_r : forall p n m, n + p < m + p <-> n < m.
Proof.
intros p n m;
setoid_replace (n + p) with (p + n) by apply plus_comm;
setoid_replace (m + p) with (p + m) by apply plus_comm;
apply plus_lt_cancel_l.
Qed.

(* The following property is similar to plus_repl_pair in NPlus.v
and is used to prove the correctness of the definition of order
on integers constructed from pairs of natural numbers *)

Theorem plus_lt_repl_pair : forall n m n' m' u v,
  n + u < m + v -> n + m' == n' + m -> n' + u < m' + v.
Proof.
intros n m n' m' u v H1 H2.
apply <- (plus_lt_cancel_r (n + m')) in H1.
set (k := n + m') in H1 at 2; rewrite H2 in H1; unfold k in H1; clear k.
rewrite <- plus_assoc in H1.
setoid_replace (m + v + (n + m')) with (n + m' + (m + v)) in H1 by apply plus_comm.
rewrite <- plus_assoc in H1. apply -> plus_lt_cancel_l in H1.
rewrite plus_assoc in H1. setoid_replace (m + v) with (v + m) in H1 by apply plus_comm.
rewrite plus_assoc in H1. apply -> plus_lt_cancel_r in H1.
now rewrite plus_comm in H1.
Qed.

Theorem plus_gt_succ :
  forall n m p, S p < n + m -> (exists n', n == S n') \/ (exists m', m == S m').
Proof.
intros n m p H.
apply <- lt_le_succ in H.
apply lt_exists_pred in H. destruct H as [q H].
now apply plus_eq_succ in H.
Qed.

End NPlusOrderProperties.


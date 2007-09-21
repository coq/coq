Require Export ZAxioms.

Module Type ZPlusSignature.
Declare Module Export ZBaseMod : ZBaseSig.
Open Local Scope IntScope.

Parameter Inline plus : Z -> Z -> Z.
Parameter Inline minus : Z -> Z -> Z.
Parameter Inline uminus : Z -> Z.

Notation "x + y" := (plus x y) : IntScope.
Notation "x - y" := (minus x y) : IntScope.
Notation "- x" := (uminus x) : IntScope.

Add Morphism plus with signature E ==> E ==> E as plus_wd.
Add Morphism minus with signature E ==> E ==> E as minus_wd.
Add Morphism uminus with signature E ==> E as uminus_wd.

Axiom plus_0 : forall n, 0 + n == n.
Axiom plus_succ : forall n m, (S n) + m == S (n + m).

Axiom minus_0 : forall n, n - 0 == n.
Axiom minus_succ : forall n m, n - (S m) == P (n - m).

Axiom uminus_0 : - 0 == 0.
Axiom uminus_succ : forall n, - (S n) == P (- n).

End ZPlusSignature.

Module ZPlusProperties (Import ZPlusModule : ZPlusSignature).
Module Export ZBasePropFunctModule := ZBasePropFunct ZBaseMod.
Open Local Scope IntScope.

Theorem plus_pred : forall n m, P n + m == P (n + m).
Proof.
intros n m. rewrite_succ_pred n at 2. rewrite plus_succ. now rewrite pred_succ.
Qed.

Theorem minus_pred : forall n m, n - (P m) == S (n - m).
Proof.
intros n m. rewrite_succ_pred m at 2. rewrite minus_succ. now rewrite succ_pred.
Qed.

Theorem uminus_pred : forall n, - (P n) == S (- n).
Proof.
intro n. rewrite_succ_pred n at 2. rewrite uminus_succ. now rewrite succ_pred.
Qed.

Theorem plus_n_0 : forall n, n + 0 == n.
Proof.
induct n.
now rewrite plus_0.
intros n IH. rewrite plus_succ. now rewrite IH.
intros n IH. rewrite plus_pred. now rewrite IH.
Qed.

Theorem plus_n_succm : forall n m, n + S m == S (n + m).
Proof.
intros n m; induct n.
now do 2 rewrite plus_0.
intros n IH. do 2 rewrite plus_succ. now rewrite IH.
intros n IH. do 2 rewrite plus_pred. rewrite IH. rewrite pred_succ; now rewrite succ_pred.
Qed.

Theorem plus_n_predm : forall n m, n + P m == P (n + m).
Proof.
intros n m; rewrite_succ_pred m at 2. rewrite plus_n_succm; now rewrite pred_succ.
Qed.

Theorem plus_opp_minus : forall n m, n + (- m) == n - m.
Proof.
induct m.
rewrite uminus_0; rewrite minus_0; now rewrite plus_n_0.
intros m IH. rewrite uminus_succ; rewrite minus_succ. rewrite plus_n_predm; now rewrite IH.
intros m IH. rewrite uminus_pred; rewrite minus_pred. rewrite plus_n_succm; now rewrite IH.
Qed.

Theorem minus_0_n : forall n, 0 - n == - n.
Proof.
intro n; rewrite <- plus_opp_minus; now rewrite plus_0.
Qed.

Theorem minus_succn_m : forall n m, S n - m == S (n - m).
Proof.
intros n m; do 2 rewrite <- plus_opp_minus; now rewrite plus_succ.
Qed.

Theorem minus_predn_m : forall n m, P n - m == P (n - m).
Proof.
intros n m. rewrite_succ_pred n at 2; rewrite minus_succn_m; now rewrite pred_succ.
Qed.

Theorem plus_assoc : forall n m p, n + (m + p) == (n + m) + p.
Proof.
intros n m p; induct n.
now do 2 rewrite plus_0.
intros n IH. do 3 rewrite plus_succ. now rewrite IH.
intros n IH. do 3 rewrite plus_pred. now rewrite IH.
Qed.

Theorem plus_comm : forall n m, n + m == m + n.
Proof.
intros n m; induct n.
rewrite plus_0; now rewrite plus_n_0.
intros n IH; rewrite plus_succ; rewrite plus_n_succm; now rewrite IH.
intros n IH; rewrite plus_pred; rewrite plus_n_predm; now rewrite IH.
Qed.

Theorem minus_diag : forall n, n - n == 0.
Proof.
induct n.
now rewrite minus_0.
intros n IH. rewrite minus_succ; rewrite minus_succn_m; rewrite pred_succ; now rewrite IH.
intros n IH. rewrite minus_pred; rewrite minus_predn_m; rewrite succ_pred; now rewrite IH.
Qed.

Theorem plus_opp_r : forall n, n + (- n) == 0.
Proof.
intro n; rewrite plus_opp_minus; now rewrite minus_diag.
Qed.

Theorem plus_opp_l : forall n, - n + n == 0.
Proof.
intro n; rewrite plus_comm; apply plus_opp_r.
Qed.

Theorem minus_swap : forall n m, - m + n == n - m.
Proof.
intros n m; rewrite <- plus_opp_minus; now rewrite plus_comm.
Qed.

Theorem plus_minus_inverse : forall n m, n + (m - n) == m.
Proof.
intros n m; rewrite <- minus_swap. rewrite plus_assoc;
rewrite plus_opp_r; now rewrite plus_0.
Qed.

Theorem plus_minus_distr : forall n m p, n + (m - p) == (n + m) - p.
Proof.
intros n m p; do 2 rewrite <- plus_opp_minus; now rewrite plus_assoc.
Qed.

Theorem double_opp : forall n, - (- n) == n.
Proof.
induct n.
now do 2 rewrite uminus_0.
intros n IH. rewrite uminus_succ; rewrite uminus_pred; now rewrite IH.
intros n IH. rewrite uminus_pred; rewrite uminus_succ; now rewrite IH.
Qed.

Theorem opp_plus_distr : forall n m, - (n + m) == - n + (- m).
Proof.
intros n m; induct n.
rewrite uminus_0; now do 2 rewrite plus_0.
intros n IH. rewrite plus_succ; do 2 rewrite uminus_succ. rewrite IH. now rewrite plus_pred.
intros n IH. rewrite plus_pred; do 2 rewrite uminus_pred. rewrite IH. now rewrite plus_succ.
Qed.

Theorem opp_minus_distr : forall n m, - (n - m) == - n + m.
Proof.
intros n m; rewrite <- plus_opp_minus; rewrite opp_plus_distr.
now rewrite double_opp.
Qed.

Theorem opp_inj : forall n m, - n == - m -> n == m.
Proof.
intros n m H. apply uminus_wd in H. now do 2 rewrite double_opp in H.
Qed.

Theorem minus_plus_distr : forall n m p, n - (m + p) == (n - m) - p.
Proof.
intros n m p; rewrite <- plus_opp_minus. rewrite opp_plus_distr. rewrite plus_assoc.
now do 2 rewrite plus_opp_minus.
Qed.

Theorem minus_minus_distr : forall n m p, n - (m - p) == (n - m) + p.
Proof.
intros n m p; rewrite <- plus_opp_minus. rewrite opp_minus_distr. rewrite plus_assoc.
now rewrite plus_opp_minus.
Qed.

Theorem plus_minus_swap : forall n m p, n + m - p == n - p + m.
Proof.
intros n m p. rewrite <- plus_minus_distr.
rewrite <- (plus_opp_minus n p). rewrite <- plus_assoc. now rewrite minus_swap.
Qed.

Theorem plus_cancel_l : forall n m p, n + m == n + p -> m == p.
Proof.
intros n m p H.
assert (H1 : - n + n + m == -n + n + p).
do 2 rewrite <- plus_assoc; now rewrite H.
rewrite plus_opp_l in H1; now do 2 rewrite plus_0 in H1.
Qed.

Theorem plus_cancel_r : forall n m p, n + m == p + m -> n == p.
Proof.
intros n m p H.
rewrite plus_comm in H. set (k := m + n) in H. rewrite plus_comm in H.
unfold k in H; clear k. now apply plus_cancel_l with m.
Qed.

Theorem plus_minus_l : forall n m p, m + p == n -> p == n - m.
Proof.
intros n m p H.
assert (H1 : - m + m + p == - m + n).
rewrite <- plus_assoc; now rewrite H.
rewrite plus_opp_l in H1. rewrite plus_0 in H1. now rewrite minus_swap in H1.
Qed.

Theorem plus_minus_r : forall n m p, m + p == n -> m == n - p.
Proof.
intros n m p H; rewrite plus_comm in H; now apply plus_minus_l in H.
Qed.

Lemma minus_eq : forall n m, n - m == 0 -> n == m.
Proof.
intros n m H. rewrite <- (plus_minus_inverse m n). rewrite H. apply plus_n_0.
Qed.

End ZPlusProperties.


(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)

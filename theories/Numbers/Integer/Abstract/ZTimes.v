Require Export ZPlus.

Module Type ZTimesSignature.
Declare Module Export ZPlusModule : ZPlusSignature.
Open Local Scope IntScope.

Parameter Inline times : Z -> Z -> Z.

Notation "x * y" := (times x y) : IntScope.

Add Morphism times with signature E ==> E ==> E as times_wd.

Axiom times_0 : forall n, n * 0 == 0.
Axiom times_succ : forall n m, n * (S m) == n * m + n.

End ZTimesSignature.

Module ZTimesProperties (Import ZTimesModule : ZTimesSignature).
Module Export ZPlusPropertiesModule := ZPlusProperties ZPlusModule.
Open Local Scope IntScope.

Theorem times_pred : forall n m, n * (P m) == n * m - n.
Proof.
intros n m. rewrite_succ_pred m at 2. rewrite times_succ. rewrite <- plus_minus_distr.
rewrite minus_diag. now rewrite plus_n_0.
Qed.

Theorem times_0_n : forall n, 0 * n == 0.
Proof.
induct n.
now rewrite times_0.
intros n IH. rewrite times_succ. rewrite IH; now rewrite plus_0.
intros n IH. rewrite times_pred. rewrite IH; now rewrite minus_0.
Qed.

Theorem times_succn_m : forall n m, (S n) * m == n * m + m.
Proof.
induct m.
do 2 rewrite times_0. now rewrite plus_0.
intros m IH. do 2 rewrite times_succ. rewrite IH.
do 2 rewrite <- plus_assoc. apply plus_wd. reflexivity.
do 2 rewrite plus_n_succm; now rewrite plus_comm.
intros m IH. do 2 rewrite times_pred. rewrite IH.
rewrite <- plus_minus_swap. do 2 rewrite <- plus_minus_distr.
apply plus_wd. reflexivity.
rewrite minus_succ. now rewrite minus_predn_m.
Qed.

Theorem times_predn_m : forall n m, (P n) * m == n * m - m.
Proof.
intros n m. rewrite_succ_pred n at 2. rewrite times_succn_m.
rewrite <- plus_minus_distr. rewrite minus_diag; now rewrite plus_n_0.
Qed.

Theorem times_comm : forall n m, n * m == m * n.
Proof.
intros n m; induct n.
rewrite times_0_n; now rewrite times_0.
intros n IH. rewrite times_succn_m; rewrite times_succ; now rewrite IH.
intros n IH. rewrite times_predn_m; rewrite times_pred; now rewrite IH.
Qed.

Theorem times_opp_r : forall n m, n * (- m) == - (n * m).
Proof.
intros n m; induct m.
rewrite uminus_0; rewrite times_0; now rewrite uminus_0.
intros m IH. rewrite uminus_succ. rewrite times_pred; rewrite times_succ. rewrite IH.
rewrite <- plus_opp_minus; now rewrite opp_plus_distr.
intros m IH. rewrite uminus_pred. rewrite times_pred; rewrite times_succ. rewrite IH.
now rewrite opp_minus_distr.
Qed.

Theorem times_opp_l : forall n m, (- n) * m == - (n * m).
Proof.
intros n m; rewrite (times_comm (- n) m); rewrite (times_comm n m);
now rewrite times_opp_r.
Qed.

Theorem times_opp_opp : forall n m, (- n) * (- m) == n * m.
Proof.
intros n m. rewrite times_opp_l. rewrite times_opp_r. now rewrite double_opp.
Qed.

Theorem times_plus_distr_r : forall n m p, n * (m + p) == n * m + n * p.
Proof.
intros n m p; induct m.
rewrite times_0; now do 2 rewrite plus_0.
intros m IH. rewrite plus_succ. do 2 rewrite times_succ. rewrite IH.
do 2 rewrite <- plus_assoc; apply plus_wd; [reflexivity | apply plus_comm].
intros m IH. rewrite plus_pred. do 2 rewrite times_pred. rewrite IH.
apply plus_minus_swap.
Qed.

Theorem times_plus_distr_l : forall n m p, (n + m) * p == n * p + m * p.
Proof.
intros n m p; rewrite (times_comm (n + m) p); rewrite times_plus_distr_r;
rewrite (times_comm p n); now rewrite (times_comm p m).
Qed.

Theorem times_minus_distr_r : forall n m p, n * (m - p) == n * m - n * p.
Proof.
intros n m p.
do 2 rewrite <- plus_opp_minus. rewrite times_plus_distr_r. now rewrite times_opp_r.
Qed.

Theorem times_minus_distr_l : forall n m p, (n - m) * p == n * p - m * p.
Proof.
intros n m p.
do 2 rewrite <- plus_opp_minus. rewrite times_plus_distr_l. now rewrite times_opp_l.
Qed.

Theorem times_assoc : forall n m p, n * (m * p) == (n * m) * p.
Proof.
intros n m p; induct p.
now do 3 rewrite times_0.
intros p IH. do 2 rewrite times_succ. rewrite times_plus_distr_r. now rewrite IH.
intros p IH. do 2 rewrite times_pred. rewrite times_minus_distr_r. now rewrite IH.
Qed.

End ZTimesProperties.


(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)

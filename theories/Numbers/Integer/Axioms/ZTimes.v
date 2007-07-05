Require Import NumPrelude.
Require Import ZDomain.
Require Import ZAxioms.
Require Import ZPlus.

Module Type TimesSignature.
Declare Module Export PlusModule : PlusSignature.
Open Local Scope ZScope.

Parameter Inline times : Z -> Z -> Z.

Notation "x * y" := (times x y) : ZScope.

Add Morphism times with signature E ==> E ==> E as times_wd.

Axiom times_0 : forall n, n * 0 == 0.
Axiom times_S : forall n m, n * (S m) == n * m + n.

(* Here recursion is done on the second argument to conform to the
usual definition of ordinal multiplication in set theory, which is not
commutative. It seems, however, that this definition in set theory is
unfortunate for two reasons. First, multiplication of two ordinals A
and B can be defined as (an order type of) the cartesian product B x A
(not A x B) ordered lexicographically. For example, omega * 2 =
2 x omega = {(0,0) < (0,1) < (0,2) < ... < (1,0) < (1,1) < (1,2) < ...},
while 2 * omega = omega x 2 = {(0,0) < (0,1) < (1,0) < (1,1) < (2,0) <
(2,1) < ...} = omega. Secondly, the way the product 2 * 3 is said in
French (deux fois trois) and Russian (dvazhdy tri) implies 3 + 3, not
2 + 2 + 2. So it would possibly be more reasonable to define multiplication
(here as well as in set theory) by recursion on the first argument. *)

End TimesSignature.

Module TimesProperties (Export TimesModule : TimesSignature).
Module Export PlusPropertiesModule := PlusProperties PlusModule.
Open Local Scope ZScope.

Theorem times_P : forall n m, n * (P m) == n * m - n.
Proof.
intros n m. rewrite_S_P m at 2. rewrite times_S. rewrite <- plus_minus_distr.
rewrite minus_diag. now rewrite plus_n_0.
Qed.

Theorem times_0_n : forall n, 0 * n == 0.
Proof.
induct n.
now rewrite times_0.
intros n IH. rewrite times_S. rewrite IH; now rewrite plus_0.
intros n IH. rewrite times_P. rewrite IH; now rewrite minus_0.
Qed.

Theorem times_Sn_m : forall n m, (S n) * m == n * m + m.
Proof.
induct m.
do 2 rewrite times_0. now rewrite plus_0.
intros m IH. do 2 rewrite times_S. rewrite IH.
do 2 rewrite <- plus_assoc. apply plus_wd. reflexivity.
do 2 rewrite plus_n_Sm; now rewrite plus_comm.
intros m IH. do 2 rewrite times_P. rewrite IH.
rewrite <- plus_minus_swap. do 2 rewrite <- plus_minus_distr.
apply plus_wd. reflexivity.
rewrite minus_S. now rewrite minus_Pn_m.
Qed.

Theorem times_Pn_m : forall n m, (P n) * m == n * m - m.
Proof.
intros n m. rewrite_S_P n at 2. rewrite times_Sn_m.
rewrite <- plus_minus_distr. rewrite minus_diag; now rewrite plus_n_0.
Qed.

Theorem times_comm : forall n m, n * m == m * n.
Proof.
intros n m; induct n.
rewrite times_0_n; now rewrite times_0.
intros n IH. rewrite times_Sn_m; rewrite times_S; now rewrite IH.
intros n IH. rewrite times_Pn_m; rewrite times_P; now rewrite IH.
Qed.

Theorem times_opp_r : forall n m, n * (- m) == - (n * m).
Proof.
intros n m; induct m.
rewrite uminus_0; rewrite times_0; now rewrite uminus_0.
intros m IH. rewrite uminus_S. rewrite times_P; rewrite times_S. rewrite IH.
rewrite <- plus_opp_minus; now rewrite opp_plus_distr.
intros m IH. rewrite uminus_P. rewrite times_P; rewrite times_S. rewrite IH.
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
intros m IH. rewrite plus_S. do 2 rewrite times_S. rewrite IH.
do 2 rewrite <- plus_assoc; apply plus_wd; [reflexivity | apply plus_comm].
intros m IH. rewrite plus_P. do 2 rewrite times_P. rewrite IH.
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
intros p IH. do 2 rewrite times_S. rewrite times_plus_distr_r. now rewrite IH.
intros p IH. do 2 rewrite times_P. rewrite times_minus_distr_r. now rewrite IH.
Qed.

End TimesProperties.

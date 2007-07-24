Require Import Ring.
Require Export NPlus.

Module Type NTimesSignature.
Declare Module Export NPlusModule : NPlusSignature.
Open Local Scope NatScope.

Parameter Inline times : N -> N -> N.

Notation "x * y" := (times x y) : NatScope.

Add Morphism times with signature E ==> E ==> E as times_wd.

Axiom times_0_n : forall n, 0 * n == 0.
Axiom times_Sn_m : forall n m, (S n) * m == m + n * m.

End NTimesSignature.

Module NTimesProperties (Import NTimesModule : NTimesSignature).
Module Export NPlusPropertiesModule := NPlusProperties NPlusModule.
Open Local Scope NatScope.

Theorem mult_0_r : forall n, n * 0 == 0.
Proof.
induct n.
now rewrite times_0_n.
intros x IH.
rewrite times_Sn_m; now rewrite plus_0_n.
Qed.

Theorem mult_0_l : forall n, 0 * n == 0.
Proof.
intro n; now rewrite times_0_n.
Qed.

Theorem mult_plus_distr_r : forall n m p, (n + m) * p == n * p + m * p.
Proof.
intros n m p; induct n.
rewrite mult_0_l.
now do 2 rewrite plus_0_l.
intros x IH.
rewrite plus_Sn_m.
do 2 rewrite times_Sn_m.
rewrite IH.
apply plus_assoc.
Qed.

Theorem mult_plus_distr_l : forall n m p, n * (m + p) == n * m + n * p.
Proof.
intros n m p; induct n.
do 3 rewrite mult_0_l; now rewrite plus_0_l.
intros x IH.
do 3 rewrite times_Sn_m.
rewrite IH.
(* Now we have to rearrange the sum of 4 terms *)
rewrite <- (plus_assoc m p (x * m + x * p)).
rewrite (plus_assoc p (x * m) (x * p)).
rewrite (plus_comm p (x * m)).
rewrite <- (plus_assoc (x * m) p (x * p)).
apply (plus_assoc m (x * m) (p + x * p)).
Qed.

Theorem mult_assoc : forall n m p, n * (m * p) == (n * m) * p.
Proof.
intros n m p; induct n.
now do 3 rewrite mult_0_l.
intros x IH.
do 2 rewrite times_Sn_m.
rewrite mult_plus_distr_r.
now rewrite IH.
Qed.

Theorem mult_1_l : forall n, 1 * n == n.
Proof.
intro n.
rewrite times_Sn_m; rewrite times_0_n. now rewrite plus_0_r.
Qed.

Theorem mult_1_r : forall n, n * 1 == n.
Proof.
induct n.
now rewrite times_0_n.
intros x IH.
rewrite times_Sn_m; rewrite IH; rewrite plus_Sn_m; now rewrite plus_0_n.
Qed.

Theorem mult_comm : forall n m, n * m == m * n.
Proof.
intros n m.
induct n.
rewrite mult_0_l; now rewrite mult_0_r.
intros x IH.
rewrite times_Sn_m.
assert (H : S x == S 0 + x).
rewrite plus_Sn_m; rewrite plus_0_n; reflexivity.
rewrite H.
rewrite mult_plus_distr_l.
rewrite mult_1_r; rewrite IH; reflexivity.
Qed.

Theorem times_eq_0 : forall n m, n * m == 0 -> n == 0 \/ m == 0.
Proof.
induct n; induct m.
intros; now left.
intros; now left.
intros; now right.
intros m IH H1.
rewrite times_Sn_m in H1; rewrite plus_Sn_m in H1; now apply S_0 in H1.
Qed.

Definition times_eq_0_dec (n m : N) : bool :=
  recursion true (fun _ _ => recursion false (fun _ _ => false) m) n.

Lemma times_eq_0_dec_wd_step :
  forall y y', y == y' ->
    eq_bool (recursion false (fun _ _ => false) y)
            (recursion false (fun _ _ => false) y').
Proof.
intros y y' Eyy'.
apply recursion_wd with (EA := eq_bool).
now unfold eq_bool.
unfold eq_fun2. intros. now unfold eq_bool.
assumption.
Qed.

Add Morphism times_eq_0_dec with signature E ==> E ==> eq_bool
as times_eq_0_dec_wd.
unfold fun2_wd, times_eq_0_dec.
intros x x' Exx' y y' Eyy'.
apply recursion_wd with (EA := eq_bool).
now unfold eq_bool.
unfold eq_fun2; intros. now apply times_eq_0_dec_wd_step.
assumption.
Qed.

Theorem times_eq_0_dec_correct :
  forall n m, n * m == 0 ->
    (times_eq_0_dec n m = true ->  n == 0) /\
    (times_eq_0_dec n m = false -> m == 0).
Proof.
nondep_induct n; nondep_induct m; unfold times_eq_0_dec.
rewrite recursion_0; split; now intros.
intro n; rewrite recursion_0; split; now intros.
intro; rewrite recursion_0; rewrite (recursion_S eq_bool);
[split; now intros | now unfold eq_bool | unfold fun2_wd; unfold eq_bool; now intros].
intro m; rewrite (recursion_S eq_bool).
rewrite times_Sn_m. rewrite plus_Sn_m. intro H; now apply S_0 in H.
now unfold eq_bool.
unfold fun2_wd; intros; now unfold eq_bool.
Qed.

Theorem times_eq_1 : forall n m, n * m == 1 -> n == 1 /\ m == 1.
Proof.
nondep_induct n; nondep_induct m.
intro H; rewrite times_0_n in H; symmetry in H; now apply S_0 in H.
intros n H; rewrite times_0_n in H; symmetry in H; now apply S_0 in H.
intro H; rewrite mult_0_r in H; symmetry in H; now apply S_0 in H.
intros m H; rewrite times_Sn_m in H; rewrite plus_Sn_m in H;
apply S_inj in H; rewrite mult_comm in H; rewrite times_Sn_m in H;
apply plus_eq_0 in H; destruct H as [H1 H2];
apply plus_eq_0 in H2; destruct H2 as [H3 _]; rewrite H1; rewrite H3; now split.
Qed.

(* See the notes on the theorem plus_repl_pair in NPlus.v *)

Theorem plus_mult_repl_pair : forall a n m n' m' u v,
  a * n + u == a * m + v -> n + m' == n' + m -> a * n' + u == a * m' + v.
Proof.
induct a.
intros; repeat rewrite times_0_n in *; now repeat rewrite plus_0_n in *.
intros a IH n m n' m' u v H1 H2.
repeat rewrite times_Sn_m in *.
(*setoid_replace (n + a * n) with (a * n + n) in H1 by (apply plus_comm).
setoid_replace (m + a * m) with (a * m + m) in H1 by (apply plus_comm).*)
setoid_replace (n' + a * n') with (a * n' + n') by (apply plus_comm).
setoid_replace (m' + a * m') with (a * m' + m') by (apply plus_comm).
do 2 rewrite <- plus_assoc. apply IH with n m; [| assumption]. do 2 rewrite plus_assoc.
setoid_replace ((a * n) + n') with (n' + a * n) by (apply plus_comm).
setoid_replace (a * m + m') with (m' + a * m) by (apply plus_comm).
do 2 rewrite <- plus_assoc. apply plus_repl_pair with n m; [| assumption].
now do 2 rewrite plus_assoc.
Qed.

Theorem semi_ring : semi_ring_theory 0 (S 0) plus times E.
Proof.
constructor.
exact plus_0_l.
exact plus_comm.
exact plus_assoc.
exact mult_1_l.
exact mult_0_l.
exact mult_comm.
exact mult_assoc.
exact mult_plus_distr_r.
Qed.

Add Ring SR : semi_ring.
Goal forall x y z : N, (x + y) * z == z * y + x * z.
intros. Set Printing All. ring.


End NTimesProperties.

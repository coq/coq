Require Export Ring.
(* Since we define a ring here, it should be possible to call the tactic
ring in the modules that use this module. Hence Export, not Import. *)
Require Export NPlus.

Module Type NTimesSignature.
Declare Module Export NPlusModule : NPlusSignature.
Open Local Scope NatScope.

Parameter Inline times : N -> N -> N.

Notation "x * y" := (times x y) : NatScope.

Add Morphism times with signature E ==> E ==> E as times_wd.

Axiom times_0_r : forall n, n * 0 == 0.
Axiom times_S_r : forall n m, n * (S m) == n * m + n.

(* Here recursion is done on the second argument to conform to the
usual definition of ordinal multiplication in set theory, which is not
commutative. It seems, however, that this definition in set theory is
unfortunate for two reasons. First, multiplication A * B of two ordinals A
and B can be defined as (an order type of) the cartesian product B x A
(not A x B) ordered lexicographically. For example, omega * 2 =
2 x omega = {(0,0) < (0,1) < (0,2) < ... < (1,0) < (1,1) < (1,2) < ...},
while 2 * omega = omega x 2 = {(0,0) < (0,1) < (1,0) < (1,1) < (2,0) <
(2,1) < ...} = omega. Secondly, the way the product 2 * 3 is said in
French (deux fois trois) and Russian (dvazhdy tri) implies 3 + 3, not
2 + 2 + 2. So it would possibly be more reasonable to define multiplication
(here as well as in set theory) by recursion on the first argument. *)

End NTimesSignature.

Module NTimesProperties (Import NTimesModule : NTimesSignature).
Module Export NPlusPropertiesModule := NPlusProperties NPlusModule.NatModule NPlusModule.
Open Local Scope NatScope.

Theorem times_0_l : forall n, 0 * n == 0.
Proof.
induct n.
now rewrite times_0_r.
intros x IH.
rewrite times_S_r. now rewrite plus_0_r.
Qed.

Theorem times_S_l : forall n m, (S n) * m == n * m + m.
Proof.
intros n m; induct m.
do 2 rewrite times_0_r; now rewrite plus_0_l.
intros m IH. do 2 rewrite times_S_r. rewrite IH.
do 2 rewrite <- plus_assoc. repeat rewrite plus_S_r.
now setoid_replace (m + n) with (n + m); [| apply plus_comm].
Qed.

Theorem times_comm : forall n m, n * m == m * n.
Proof.
intros n m. induct n.
rewrite times_0_l; now rewrite times_0_r.
intros n IH. rewrite times_S_l; rewrite times_S_r. now rewrite IH.
Qed.

Theorem times_plus_distr_r : forall n m p, (n + m) * p == n * p + m * p.
Proof.
intros n m p; induct n.
rewrite times_0_l. now do 2 rewrite plus_0_l.
intros n IH. rewrite plus_S_l. do 2 rewrite times_S_l. rewrite IH.
do 2 rewrite <- plus_assoc. apply plus_wd. reflexivity. apply plus_comm.
Qed.

Theorem times_plus_distr_l : forall n m p, n * (m + p) == n * m + n * p.
Proof.
intros n m p.
setoid_replace (n * (m + p)) with ((m + p) * n); [| apply times_comm].
rewrite times_plus_distr_r.
setoid_replace (n * m) with (m * n); [| apply times_comm].
now setoid_replace (n * p) with (p * n); [| apply times_comm].
Qed.

Theorem times_assoc : forall n m p, n * (m * p) == (n * m) * p.
Proof.
intros n m p; induct n.
now repeat rewrite times_0_l.
intros n IH. do 2 rewrite times_S_l. rewrite IH. now rewrite times_plus_distr_r.
Qed.

Theorem times_1_l : forall n, 1 * n == n.
Proof.
intro n. rewrite times_S_l; rewrite times_0_l. now rewrite plus_0_l.
Qed.

Theorem times_1_r : forall n, n * 1 == n.
Proof.
intro n; rewrite times_comm; apply times_1_l.
Qed.

Lemma semi_ring : semi_ring_theory 0 (S 0) plus times E.
Proof.
constructor.
exact plus_0_l.
exact plus_comm.
exact plus_assoc.
exact times_1_l.
exact times_0_l.
exact times_comm.
exact times_assoc.
exact times_plus_distr_r.
Qed.

Add Ring SR : semi_ring.

Theorem times_eq_0 : forall n m, n * m == 0 -> n == 0 \/ m == 0.
Proof.
induct n; induct m.
intros; now left.
intros; now left.
intros; now right.
intros m IH H1. rewrite times_S_l in H1. rewrite plus_S_r in H1. now apply S_0 in H1.
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
rewrite times_S_l. rewrite plus_S_r. intro H; now apply S_0 in H.
now unfold eq_bool.
unfold fun2_wd; intros; now unfold eq_bool.
Qed.

Theorem times_eq_1 : forall n m, n * m == 1 -> n == 1 /\ m == 1.
Proof.
nondep_induct n; nondep_induct m.
intro H; rewrite times_0_l in H; symmetry in H; now apply S_0 in H.
intros n H; rewrite times_0_l in H; symmetry in H; now apply S_0 in H.
intro H; rewrite times_0_r in H; symmetry in H; now apply S_0 in H.
intros m H; rewrite times_S_l in H; rewrite plus_S_r in H;
apply S_inj in H; rewrite times_comm in H; rewrite times_S_l in H;
apply plus_eq_0 in H; destruct H as [H1 H2].
apply plus_eq_0 in H1; destruct H1 as [_ H3]; rewrite H2; rewrite H3; now split.
Qed.

(* In proving the correctness of the definition of multiplication on
integers constructed from pairs of natural numbers, we'll need the
following fact about natural numbers:

a * x + u == a * y + v -> x + y' == x' + y -> a * x' + u = a * y' + v  (2)

Here x + y' == x' + y represents equality of integers (x, y) and
(x', y'), since a pair of natural numbers represents their integer
difference. On integers, the (2) could be proved by moving
a * y to the left, factoring out a and replacing x - y by x' - y'.
However, the whole point is that we are only in the process of
constructing integers, so this has to be proved for natural numbers,
where we cannot move terms from one side of an equation to the other.
This can be proved using the cancellation law plus_cancel_l. *)

Theorem plus_times_repl_pair : forall a n m n' m' u v,
  a * n + u == a * m + v -> n + m' == n' + m -> a * n' + u == a * m' + v.
Proof.
intros a n m n' m' u v H1 H2.
apply (times_wd a a) in H2; [| reflexivity].
do 2 rewrite times_plus_distr_l in H2.
symmetry in H2; add_equations H1 H2 as H3.
stepl (a * n + (u + a * n' + a * m)) in H3 by ring.
stepr (a * n + (a * m + v + a * m')) in H3 by ring.
apply plus_cancel_l in H3.
stepl (a * m + (u + a * n')) in H3 by ring.
stepr (a * m + (v + a * m')) in H3 by ring.
apply plus_cancel_l in H3.
stepl (u + a * n') by ring. now stepr (v + a * m') by ring.
Qed.

End NTimesProperties.

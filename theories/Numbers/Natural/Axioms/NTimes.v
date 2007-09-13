Require Export Ring.
(* Since we define a ring below, it should be possible to call the tactic
ring in the modules that use this module. Hence Export, not Import. *)
Require Export NPlus.
Require Import NZTimes.

Module Type NTimesSig.
Declare Module Export NPlusMod : NPlusSig.
Open Local Scope NatScope.

Parameter Inline times : N -> N -> N.

Notation "x * y" := (times x y) : NatScope.

Add Morphism times with signature E ==> E ==> E as times_wd.

Axiom times_0_r : forall n, n * 0 == 0.
Axiom times_succ_r : forall n m, n * (S m) == n * m + n.

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

End NTimesSig.

Module NTimesPropFunct (Import NTimesMod : NTimesSig).
Module Export NPlusPropMod := NPlusPropFunct NPlusMod.
Open Local Scope NatScope.

(*Theorem times_wd : fun2_wd E E E times.
Proof times_wd.

Theorem times_0_r : forall n, n * 0 == 0.
Proof times_0_r.

Theorem times_succ_r : forall n m, n * (S m) == n * m + n.
Proof times_succ_r.*)

Module NZTimesMod <: NZTimesSig.
Module NZPlusMod <: NZPlusSig := NZPlusMod.
Definition NZtimes := times.

(* Axioms *)

Add Morphism NZtimes with signature E ==> E ==> E as NZtimes_wd.
Proof times_wd.
Definition NZtimes_0_r := times_0_r.
Definition NZtimes_succ_r := times_succ_r.

End NZTimesMod.

Module Export NZTimesPropMod := NZTimesPropFunct NZTimesMod.

(** Theorems that are valid for both natural numbers and integers *)

Theorem times_0_l : forall n : N, 0 * n == 0.
Proof NZtimes_0_l.

Theorem times_succ_l : forall n m : N, (S n) * m == n * m + m.
Proof NZtimes_succ_l.

Theorem times_comm : forall n m : N, n * m == m * n.
Proof NZtimes_comm.

Theorem times_plus_distr_r : forall n m p : N, (n + m) * p == n * p + m * p.
Proof NZtimes_plus_distr_r.

Theorem times_plus_distr_l : forall n m p : N, n * (m + p) == n * m + n * p.
Proof NZtimes_plus_distr_l.

Theorem times_assoc : forall n m p : N, n * (m * p) == (n * m) * p.
Proof NZtimes_assoc.

Theorem times_1_l : forall n : N, 1 * n == n.
Proof NZtimes_1_l.

Theorem times_1_r : forall n : N, n * 1 == n.
Proof NZtimes_1_r.

Lemma semi_ring : semi_ring_theory 0 1 plus times E.
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

(** Theorems that cannot be proved in NZTimes *)

Theorem times_eq_0 : forall n m, n * m == 0 -> n == 0 \/ m == 0.
Proof.
induct n; induct m.
intros; now left.
intros; now left.
intros; now right.
intros m IH H1. rewrite times_succ_l in H1.
rewrite plus_succ_r in H1. now apply succ_neq_0 in H1.
Qed.

Theorem times_eq_1 : forall n m, n * m == 1 -> n == 1 /\ m == 1.
Proof.
intros n m; induct n.
intro H; rewrite times_0_l in H; symmetry in H; false_hyp H succ_neq_0.
intros n IH H. rewrite times_succ_l in H. apply plus_eq_1 in H.
destruct H as [[H1 H2] | [H1 H2]].
apply IH in H1. destruct H1 as [_ H1]. rewrite H1 in H2; false_hyp H2 succ_neq_0.
apply times_eq_0 in H1. destruct H1 as [H1 | H1].
rewrite H1; now split.
rewrite H2 in H1; false_hyp H1 succ_neq_0.
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
apply -> plus_cancel_l in H3.
stepl (a * m + (u + a * n')) in H3 by ring.
stepr (a * m + (v + a * m')) in H3 by ring.
apply -> plus_cancel_l in H3.
stepl (u + a * n') by ring. now stepr (v + a * m') by ring.
Qed.

End NTimesPropFunct.


(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

(*i i*)

Require Export NPlus.

Module NTimesPropFunct (Import NAxiomsMod : NAxiomsSig).
Module Export NPlusPropMod := NPlusPropFunct NAxiomsMod.
Open Local Scope NatScope.

Theorem times_wd :
  forall n1 n2 : N, n1 == n2 -> forall m1 m2 : N, m1 == m2 -> n1 * m1 == n2 * m2.
Proof NZtimes_wd.

Theorem times_0_l : forall n : N, 0 * n == 0.
Proof NZtimes_0_l.

Theorem times_succ_l : forall n m : N, (S n) * m == n * m + m.
Proof NZtimes_succ_l.

(** Theorems that are valid for both natural numbers and integers *)

Theorem times_0_r : forall n, n * 0 == 0.
Proof NZtimes_0_r.

Theorem times_succ_r : forall n m, n * (S m) == n * m + n.
Proof NZtimes_succ_r.

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

(* Theorems that cannot be proved in NZTimes *)

(* In proving the correctness of the definition of multiplication on
integers constructed from pairs of natural numbers, we'll need the
following fact about natural numbers:

a * n + u == a * m + v -> n + m' == n' + m -> a * n' + u = a * m' + v

Here n + m' == n' + m expresses equality of integers (n, m) and (n', m'),
since a pair (a, b) of natural numbers represents the integer a - b. On
integers, the formula above could be proved by moving a * m to the left,
factoring out a and replacing n - m by n' - m'. However, the formula is
required in the process of constructing integers, so it has to be proved
for natural numbers, where terms cannot be moved from one side of an
equation to the other. The proof uses the cancellation laws plus_cancel_l
and plus_cancel_r. *)

Theorem plus_times_repl_pair : forall a n m n' m' u v : N,
  a * n + u == a * m + v -> n + m' == n' + m -> a * n' + u == a * m' + v.
Proof.
intros a n m n' m' u v H1 H2.
apply (@NZtimes_wd a a) in H2; [| reflexivity].
do 2 rewrite times_plus_distr_l in H2. symmetry in H2.
pose proof (NZplus_wd _ _ H1 _ _ H2) as H3.
rewrite (plus_shuffle1 (a * m)), (plus_comm (a * m) (a * n)) in H3.
do 2 rewrite <- plus_assoc in H3. apply -> plus_cancel_l in H3.
rewrite (plus_assoc u), (plus_comm (a * m)) in H3.
apply -> plus_cancel_r in H3.
now rewrite (plus_comm (a * n') u), (plus_comm (a * m') v).
Qed.

End NTimesPropFunct.


(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Orders BinPos Pnat POrderedType GenericMinMax.

(** * Maximum and Minimum of two positive numbers *)

Local Open Scope positive_scope.

(** The functions [Pmax] and [Pmin] implement indeed
    a maximum and a minimum *)

Lemma Pmax_l : forall x y, y<=x -> Pmax x y = x.
Proof.
 unfold Ple, Pmax. intros x y.
 rewrite (ZC4 y x). generalize (Pcompare_eq_iff x y).
 destruct ((x ?= y) Eq); intuition.
Qed.

Lemma Pmax_r : forall x y, x<=y -> Pmax x y = y.
Proof.
 unfold Ple, Pmax. intros x y. destruct ((x ?= y) Eq); intuition.
Qed.

Lemma Pmin_l : forall x y, x<=y -> Pmin x y = x.
Proof.
 unfold Ple, Pmin. intros x y. destruct ((x ?= y) Eq); intuition.
Qed.

Lemma Pmin_r : forall x y, y<=x -> Pmin x y = y.
Proof.
 unfold Ple, Pmin. intros x y.
 rewrite (ZC4 y x). generalize (Pcompare_eq_iff x y).
 destruct ((x ?= y) Eq); intuition.
Qed.

Module PositiveHasMinMax <: HasMinMax Positive_as_OT.
 Definition max := Pmax.
 Definition min := Pmin.
 Definition max_l := Pmax_l.
 Definition max_r := Pmax_r.
 Definition min_l := Pmin_l.
 Definition min_r := Pmin_r.
End PositiveHasMinMax.


Module P.
(** We obtain hence all the generic properties of max and min. *)

Include UsualMinMaxProperties Positive_as_OT PositiveHasMinMax.

(** * Properties specific to the [positive] domain *)

(** Simplifications *)

Lemma max_1_l : forall n, Pmax 1 n = n.
Proof.
 intros. unfold Pmax. rewrite ZC4. generalize (Pcompare_1 n).
 destruct (n ?= 1); intuition.
Qed.

Lemma max_1_r : forall n, Pmax n 1 = n.
Proof. intros. rewrite P.max_comm. apply max_1_l. Qed.

Lemma min_1_l : forall n, Pmin 1 n = 1.
Proof.
 intros. unfold Pmin. rewrite ZC4. generalize (Pcompare_1 n).
 destruct (n ?= 1); intuition.
Qed.

Lemma min_1_r : forall n, Pmin n 1 = 1.
Proof. intros. rewrite P.min_comm. apply min_1_l. Qed.

(** Compatibilities (consequences of monotonicity) *)

Lemma succ_max_distr :
 forall n m, Psucc (Pmax n m) = Pmax (Psucc n) (Psucc m).
Proof.
 intros. symmetry. apply max_monotone.
 intros x x'. unfold Ple.
 rewrite 2 nat_of_P_compare_morphism, 2 nat_of_P_succ_morphism.
 simpl; auto.
Qed.

Lemma succ_min_distr : forall n m, Psucc (Pmin n m) = Pmin (Psucc n) (Psucc m).
Proof.
 intros. symmetry. apply min_monotone.
 intros x x'. unfold Ple.
 rewrite 2 nat_of_P_compare_morphism, 2 nat_of_P_succ_morphism.
 simpl; auto.
Qed.

Lemma plus_max_distr_l : forall n m p, Pmax (p + n) (p + m) = p + Pmax n m.
Proof.
 intros. apply max_monotone.
 intros x x'. unfold Ple.
 rewrite 2 nat_of_P_compare_morphism, 2 nat_of_P_plus_morphism.
 rewrite <- 2 Compare_dec.nat_compare_le. auto with arith.
Qed.

Lemma plus_max_distr_r : forall n m p, Pmax (n + p) (m + p) = Pmax n m + p.
Proof.
 intros. rewrite (Pplus_comm n p), (Pplus_comm m p), (Pplus_comm _ p).
 apply plus_max_distr_l.
Qed.

Lemma plus_min_distr_l : forall n m p, Pmin (p + n) (p + m) = p + Pmin n m.
Proof.
 intros. apply min_monotone.
 intros x x'. unfold Ple.
 rewrite 2 nat_of_P_compare_morphism, 2 nat_of_P_plus_morphism.
 rewrite <- 2 Compare_dec.nat_compare_le. auto with arith.
Qed.

Lemma plus_min_distr_r : forall n m p, Pmin (n + p) (m + p) = Pmin n m + p.
Proof.
 intros. rewrite (Pplus_comm n p), (Pplus_comm m p), (Pplus_comm _ p).
 apply plus_min_distr_l.
Qed.

End P.
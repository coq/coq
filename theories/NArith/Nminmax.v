(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Orders BinNat Nnat NOrderedType GenericMinMax.

(** * Maximum and Minimum of two [N] numbers *)

Local Open Scope N_scope.

(** The functions [Nmax] and [Nmin] implement indeed
    a maximum and a minimum *)

Lemma Nmax_l : forall x y, y<=x -> Nmax x y = x.
Proof.
 unfold Nle, Nmax. intros x y.
 generalize (Ncompare_eq_correct x y). rewrite <- (Ncompare_antisym x y).
 destruct (x ?= y); intuition.
Qed.

Lemma Nmax_r : forall x y, x<=y -> Nmax x y = y.
Proof.
 unfold Nle, Nmax. intros x y. destruct (x ?= y); intuition.
Qed.

Lemma Nmin_l : forall x y, x<=y -> Nmin x y = x.
Proof.
 unfold Nle, Nmin. intros x y. destruct (x ?= y); intuition.
Qed.

Lemma Nmin_r : forall x y, y<=x -> Nmin x y = y.
Proof.
 unfold Nle, Nmin. intros x y.
 generalize (Ncompare_eq_correct x y). rewrite <- (Ncompare_antisym x y).
 destruct (x ?= y); intuition.
Qed.

Module NHasMinMax <: HasMinMax N_as_OT.
 Definition max := Nmax.
 Definition min := Nmin.
 Definition max_l := Nmax_l.
 Definition max_r := Nmax_r.
 Definition min_l := Nmin_l.
 Definition min_r := Nmin_r.
End NHasMinMax.

Module N.

(** We obtain hence all the generic properties of max and min. *)

Include UsualMinMaxProperties N_as_OT NHasMinMax.

(** * Properties specific to the [positive] domain *)

(** Simplifications *)

Lemma max_0_l : forall n, Nmax 0 n = n.
Proof.
 intros. unfold Nmax. rewrite <- Ncompare_antisym. generalize (Ncompare_0 n).
 destruct (n ?= 0); intuition.
Qed.

Lemma max_0_r : forall n, Nmax n 0 = n.
Proof. intros. rewrite N.max_comm. apply max_0_l. Qed.

Lemma min_0_l : forall n, Nmin 0 n = 0.
Proof.
 intros. unfold Nmin. rewrite <- Ncompare_antisym. generalize (Ncompare_0 n).
 destruct (n ?= 0); intuition.
Qed.

Lemma min_0_r : forall n, Nmin n 0 = 0.
Proof. intros. rewrite N.min_comm. apply min_0_l. Qed.

(** Compatibilities (consequences of monotonicity) *)

Lemma succ_max_distr :
 forall n m, Nsucc (Nmax n m) = Nmax (Nsucc n) (Nsucc m).
Proof.
 intros. symmetry. apply max_monotone.
 intros x x'. unfold Nle.
 rewrite 2 nat_of_Ncompare, 2 nat_of_Nsucc.
 simpl; auto.
Qed.

Lemma succ_min_distr : forall n m, Nsucc (Nmin n m) = Nmin (Nsucc n) (Nsucc m).
Proof.
 intros. symmetry. apply min_monotone.
 intros x x'. unfold Nle.
 rewrite 2 nat_of_Ncompare, 2 nat_of_Nsucc.
 simpl; auto.
Qed.

Lemma plus_max_distr_l : forall n m p, Nmax (p + n) (p + m) = p + Nmax n m.
Proof.
 intros. apply max_monotone.
 intros x x'. unfold Nle.
 rewrite 2 nat_of_Ncompare, 2 nat_of_Nplus.
 rewrite <- 2 Compare_dec.nat_compare_le. auto with arith.
Qed.

Lemma plus_max_distr_r : forall n m p, Nmax (n + p) (m + p) = Nmax n m + p.
Proof.
 intros. rewrite (Nplus_comm n p), (Nplus_comm m p), (Nplus_comm _ p).
 apply plus_max_distr_l.
Qed.

Lemma plus_min_distr_l : forall n m p, Nmin (p + n) (p + m) = p + Nmin n m.
Proof.
 intros. apply min_monotone.
 intros x x'. unfold Nle.
 rewrite 2 nat_of_Ncompare, 2 nat_of_Nplus.
 rewrite <- 2 Compare_dec.nat_compare_le. auto with arith.
Qed.

Lemma plus_min_distr_r : forall n m p, Nmin (n + p) (m + p) = Nmin n m + p.
Proof.
 intros. rewrite (Nplus_comm n p), (Nplus_comm m p), (Nplus_comm _ p).
 apply plus_min_distr_l.
Qed.

End N.
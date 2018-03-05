(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Orders Rbase Rbasic_fun ROrderedType GenericMinMax.

(** * Maximum and Minimum of two real numbers *)

Local Open Scope R_scope.

(** The functions [Rmax] and [Rmin] implement indeed
    a maximum and a minimum *)

Lemma Rmax_l : forall x y, y<=x -> Rmax x y = x.
Proof.
 unfold Rmax. intros.
 destruct Rle_dec as [H'|H']; [| apply Rnot_le_lt in H' ];
  unfold Rle in *; intuition.
Qed.

Lemma Rmax_r : forall x y, x<=y -> Rmax x y = y.
Proof.
 unfold Rmax. intros.
 destruct Rle_dec as [H'|H']; [| apply Rnot_le_lt in H' ];
  unfold Rle in *; intuition.
Qed.

Lemma Rmin_l : forall x y, x<=y -> Rmin x y = x.
Proof.
 unfold Rmin. intros.
 destruct Rle_dec as [H'|H']; [| apply Rnot_le_lt in H' ];
  unfold Rle in *; intuition.
Qed.

Lemma Rmin_r : forall x y, y<=x -> Rmin x y = y.
Proof.
 unfold Rmin. intros.
 destruct Rle_dec as [H'|H']; [| apply Rnot_le_lt in H' ];
  unfold Rle in *; intuition.
Qed.

Module RHasMinMax <: HasMinMax R_as_OT.
 Definition max := Rmax.
 Definition min := Rmin.
 Definition max_l := Rmax_l.
 Definition max_r := Rmax_r.
 Definition min_l := Rmin_l.
 Definition min_r := Rmin_r.
End RHasMinMax.

Module R.

(** We obtain hence all the generic properties of max and min. *)

Include UsualMinMaxProperties R_as_OT RHasMinMax.

(** * Properties specific to the [R] domain *)

(** Compatibilities (consequences of monotonicity) *)

Lemma plus_max_distr_l : forall n m p, Rmax (p + n) (p + m) = p + Rmax n m.
Proof.
 intros. apply max_monotone.
 intros x y. apply Rplus_le_compat_l.
Qed.

Lemma plus_max_distr_r : forall n m p, Rmax (n + p) (m + p) = Rmax n m + p.
Proof.
 intros. rewrite (Rplus_comm n p), (Rplus_comm m p), (Rplus_comm _ p).
 apply plus_max_distr_l.
Qed.

Lemma plus_min_distr_l : forall n m p, Rmin (p + n) (p + m) = p + Rmin n m.
Proof.
 intros. apply min_monotone.
 intros x y. apply Rplus_le_compat_l.
Qed.

Lemma plus_min_distr_r : forall n m p, Rmin (n + p) (m + p) = Rmin n m + p.
Proof.
 intros. rewrite (Rplus_comm n p), (Rplus_comm m p), (Rplus_comm _ p).
 apply plus_min_distr_l.
Qed.

(** Anti-monotonicity swaps the role of [min] and [max] *)

Lemma opp_max_distr : forall n m : R, -(Rmax n m) = Rmin (- n) (- m).
Proof.
 intros. symmetry. apply min_max_antimonotone.
 do 3 red. intros; apply Rge_le. apply Ropp_le_ge_contravar; auto.
Qed.

Lemma opp_min_distr : forall n m : R, - (Rmin n m) = Rmax (- n) (- m).
Proof.
 intros. symmetry. apply max_min_antimonotone.
 do 3 red. intros; apply Rge_le. apply Ropp_le_ge_contravar; auto.
Qed.

Lemma minus_max_distr_l : forall n m p, Rmax (p - n) (p - m) = p - Rmin n m.
Proof.
 unfold Rminus. intros. rewrite opp_min_distr. apply plus_max_distr_l.
Qed.

Lemma minus_max_distr_r : forall n m p, Rmax (n - p) (m - p) = Rmax n m - p.
Proof.
 unfold Rminus. intros. apply plus_max_distr_r.
Qed.

Lemma minus_min_distr_l : forall n m p, Rmin (p - n) (p - m) = p - Rmax n m.
Proof.
 unfold Rminus. intros. rewrite opp_max_distr. apply plus_min_distr_l.
Qed.

Lemma minus_min_distr_r : forall n m p, Rmin (n - p) (m - p) = Rmin n m - p.
Proof.
 unfold Rminus. intros. apply plus_min_distr_r.
Qed.

End R.

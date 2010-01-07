(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Orders BinInt Zcompare Zorder ZOrderedType
 GenericMinMax.

(** * Maximum and Minimum of two [Z] numbers *)

Local Open Scope Z_scope.

Unboxed Definition Zmax (n m:Z) :=
  match n ?= m with
    | Eq | Gt => n
    | Lt => m
  end.

Unboxed Definition Zmin (n m:Z) :=
  match n ?= m with
    | Eq | Lt => n
    | Gt => m
  end.

(** The functions [Zmax] and [Zmin] implement indeed
    a maximum and a minimum *)

Lemma Zmax_l : forall x y, y<=x -> Zmax x y = x.
Proof.
 unfold Zle, Zmax. intros x y. rewrite <- (Zcompare_antisym x y).
 destruct (x ?= y); intuition.
Qed.

Lemma Zmax_r : forall x y, x<=y -> Zmax x y = y.
Proof.
 unfold Zle, Zmax. intros x y. generalize (Zcompare_Eq_eq x y).
 destruct (x ?= y); intuition.
Qed.

Lemma Zmin_l : forall x y, x<=y -> Zmin x y = x.
Proof.
 unfold Zle, Zmin. intros x y. generalize (Zcompare_Eq_eq x y).
 destruct (x ?= y); intuition.
Qed.

Lemma Zmin_r : forall x y, y<=x -> Zmin x y = y.
Proof.
 unfold Zle, Zmin. intros x y.
 rewrite <- (Zcompare_antisym x y). generalize (Zcompare_Eq_eq x y).
 destruct (x ?= y); intuition.
Qed.

Module ZHasMinMax <: HasMinMax Z_as_OT.
 Definition max := Zmax.
 Definition min := Zmin.
 Definition max_l := Zmax_l.
 Definition max_r := Zmax_r.
 Definition min_l := Zmin_l.
 Definition min_r := Zmin_r.
End ZHasMinMax.

Module Z.

(** We obtain hence all the generic properties of max and min. *)

Include UsualMinMaxProperties Z_as_OT ZHasMinMax.

(** * Properties specific to the [Z] domain *)

(** Compatibilities (consequences of monotonicity) *)

Lemma plus_max_distr_l : forall n m p, Zmax (p + n) (p + m) = p + Zmax n m.
Proof.
 intros. apply max_monotone.
 intros x y. apply Zplus_le_compat_l.
Qed.

Lemma plus_max_distr_r : forall n m p, Zmax (n + p) (m + p) = Zmax n m + p.
Proof.
 intros. rewrite (Zplus_comm n p), (Zplus_comm m p), (Zplus_comm _ p).
 apply plus_max_distr_l.
Qed.

Lemma plus_min_distr_l : forall n m p, Zmin (p + n) (p + m) = p + Zmin n m.
Proof.
 intros. apply Z.min_monotone.
 intros x y. apply Zplus_le_compat_l.
Qed.

Lemma plus_min_distr_r : forall n m p, Zmin (n + p) (m + p) = Zmin n m + p.
Proof.
 intros. rewrite (Zplus_comm n p), (Zplus_comm m p), (Zplus_comm _ p).
 apply plus_min_distr_l.
Qed.

Lemma succ_max_distr : forall n m, Zsucc (Zmax n m) = Zmax (Zsucc n) (Zsucc m).
Proof.
 unfold Zsucc. intros. symmetry. apply plus_max_distr_r.
Qed.

Lemma succ_min_distr : forall n m, Zsucc (Zmin n m) = Zmin (Zsucc n) (Zsucc m).
Proof.
 unfold Zsucc. intros. symmetry. apply plus_min_distr_r.
Qed.

Lemma pred_max_distr : forall n m, Zpred (Zmax n m) = Zmax (Zpred n) (Zpred m).
Proof.
 unfold Zpred. intros. symmetry. apply plus_max_distr_r.
Qed.

Lemma pred_min_distr : forall n m, Zsucc (Zmin n m) = Zmin (Zsucc n) (Zsucc m).
Proof.
 unfold Zpred. intros. symmetry. apply plus_min_distr_r.
Qed.

(** Anti-monotonicity swaps the role of [min] and [max] *)

Lemma opp_max_distr : forall n m : Z, -(Zmax n m) = Zmin (- n) (- m).
Proof.
 intros. symmetry. apply min_max_antimonotone.
 intros x x'. red. red. rewrite <- Zcompare_opp; auto.
Qed.

Lemma opp_min_distr : forall n m : Z, - (Zmin n m) = Zmax (- n) (- m).
Proof.
 intros. symmetry. apply max_min_antimonotone.
 intros x x'. red. red. rewrite <- Zcompare_opp; auto.
Qed.

Lemma minus_max_distr_l : forall n m p, Zmax (p - n) (p - m) = p - Zmin n m.
Proof.
 unfold Zminus. intros. rewrite opp_min_distr. apply plus_max_distr_l.
Qed.

Lemma minus_max_distr_r : forall n m p, Zmax (n - p) (m - p) = Zmax n m - p.
Proof.
 unfold Zminus. intros. apply plus_max_distr_r.
Qed.

Lemma minus_min_distr_l : forall n m p, Zmin (p - n) (p - m) = p - Zmax n m.
Proof.
 unfold Zminus. intros. rewrite opp_max_distr. apply plus_min_distr_l.
Qed.

Lemma minus_min_distr_r : forall n m p, Zmin (n - p) (m - p) = Zmin n m - p.
Proof.
 unfold Zminus. intros. apply plus_min_distr_r.
Qed.

(** Compatibility with [Zpos] *)

Lemma pos_max : forall p q, Zpos (Pmax p q) = Zmax (Zpos p) (Zpos q).
Proof.
 intros; unfold Zmax, Pmax; simpl; generalize (Pcompare_Eq_eq p q).
 destruct Pcompare; auto.
 intro H; rewrite H; auto.
Qed.

Lemma pos_min : forall p q, Zpos (Pmin p q) = Zmin (Zpos p) (Zpos q).
Proof.
 intros; unfold Zmin, Pmin; simpl; generalize (Pcompare_Eq_eq p q).
 destruct Pcompare; auto.
Qed.

Lemma pos_max_1 : forall p, Zmax 1 (Zpos p) = Zpos p.
Proof.
  intros; unfold Zmax; simpl; destruct p; simpl; auto.
Qed.

Lemma pos_min_1 : forall p, Zmin 1 (Zpos p) = 1.
Proof.
  intros; unfold Zmax; simpl; destruct p; simpl; auto.
Qed.

End Z.


(** * Characterization of Pminus in term of Zminus and Zmax *)

Lemma Zpos_minus : forall p q, Zpos (Pminus p q) = Zmax 1 (Zpos p - Zpos q).
Proof.
  intros; simpl. destruct (Pcompare p q Eq) as [ ]_eqn:H.
  rewrite (Pcompare_Eq_eq _ _ H).
  unfold Pminus; rewrite Pminus_mask_diag; reflexivity.
  rewrite Pminus_Lt; auto.
  symmetry. apply Z.pos_max_1.
Qed.


(*begin hide*)
(* Compatibility with names of the old Zminmax file *)
Notation Zmin_max_absorption_r_r := Z.min_max_absorption (only parsing).
Notation Zmax_min_absorption_r_r := Z.max_min_absorption (only parsing).
Notation Zmax_min_distr_r := Z.max_min_distr (only parsing).
Notation Zmin_max_distr_r := Z.min_max_distr (only parsing).
Notation Zmax_min_modular_r := Z.max_min_modular (only parsing).
Notation Zmin_max_modular_r := Z.min_max_modular (only parsing).
Notation max_min_disassoc := Z.max_min_disassoc (only parsing).
(*end hide*)
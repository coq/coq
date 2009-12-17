(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import OrderedType2 BinInt Zcompare Zorder ZOrderedType
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

Lemma Zmax_spec : forall x y,
  (x<y /\ Zmax x y = y)  \/  (y<=x /\ Zmax x y = x).
Proof.
 unfold Zlt, Zle, Zmax. intros.
 generalize (Zcompare_Eq_eq x y).
 rewrite <- (Zcompare_antisym x y).
 destruct (x ?= y); simpl; auto; right; intuition; discriminate.
Qed.

Lemma Zmin_spec : forall x y,
  (x<y /\ Zmin x y = x)  \/  (y<=x /\ Zmin x y = y).
Proof.
 unfold Zlt, Zle, Zmin. intros.
 generalize (Zcompare_Eq_eq x y).
 rewrite <- (Zcompare_antisym x y).
 destruct (x ?= y); simpl; auto; right; intuition; discriminate.
Qed.

Module ZHasMinMax <: HasMinMax Z_as_OT.
 Definition max := Zmax.
 Definition min := Zmin.
 Definition max_spec := Zmax_spec.
 Definition min_spec := Zmin_spec.
End ZHasMinMax.

(** We obtain hence all the generic properties of max and min. *)

Module Import ZMinMaxProps := MinMaxProperties Z_as_OT ZHasMinMax.

(** For some generic properties, we can have nicer statements here,
    since underlying equality is Leibniz. *)

Lemma Zmax_case_strong : forall n m (P:Z -> Type),
  (m<=n -> P n) -> (n<=m -> P m) -> P (Zmax n m).
Proof. intros; apply max_case_strong; auto. congruence. Defined.

Lemma Zmax_case : forall n m (P:Z -> Type),
  P n -> P m -> P (Zmax n m).
Proof. intros. apply Zmax_case_strong; auto. Defined.

Lemma Zmax_monotone: forall f,
 (Proper (Zle ==> Zle) f) ->
 forall x y, Zmax (f x) (f y) = f (Zmax x y).
Proof. intros; apply max_monotone; auto. congruence. Qed.

Lemma Zmin_case_strong : forall n m (P:Z -> Type),
  (n<=m -> P n) -> (m<=n -> P m) -> P (Zmin n m).
Proof. intros; apply min_case_strong; auto. congruence. Defined.

Lemma Zmin_case : forall n m (P:Z -> Type),
  P n -> P m -> P (Zmin n m).
Proof. intros. apply Zmin_case_strong; auto. Defined.

Lemma Zmin_monotone: forall f,
 (Proper (Zle ==> Zle) f) ->
 forall x y, Zmin (f x) (f y) = f (Zmin x y).
Proof. intros; apply min_monotone; auto. congruence. Qed.

Lemma Zmax_min_antimonotone : forall f,
 Proper (Zle==>Zge) f ->
 forall x y, Zmax (f x) (f y) == f (Zmin x y).
Proof.
 intros. apply max_min_antimonotone. congruence.
 intros z z' Hz; red. apply Zge_le. auto.
Qed.

Lemma Zmin_max_antimonotone : forall f,
 Proper (Zle==>Zge) f ->
 forall x y, Zmin (f x) (f y) == f (Zmax x y).
Proof.
 intros. apply min_max_antimonotone. congruence.
 intros z z' Hz; red. apply Zge_le. auto.
Qed.

(** For the other generic properties, we make aliases,
   since otherwise SearchAbout misses some of them
   (bad interaction with an Include).
   See GenericMinMax (or SearchAbout) for the statements. *)

Definition Zmax_spec_le := max_spec_le.
Definition Zmax_dec := max_dec.
Definition Zmax_unicity := max_unicity.
Definition Zmax_unicity_ext := max_unicity_ext.
Definition Zmax_id := max_id.
Notation Zmax_idempotent := Zmax_id (only parsing).
Definition Zmax_assoc := max_assoc.
Definition Zmax_comm := max_comm.
Definition Zmax_l := max_l.
Definition Zmax_r := max_r.
Definition Zle_max_l := le_max_l.
Definition Zle_max_r := le_max_r.
Definition Zmax_le := max_le.
Definition Zmax_le_iff := max_le_iff.
Definition Zmax_lt_iff := max_lt_iff.
Definition Zmax_lub_l := max_lub_l.
Definition Zmax_lub_r := max_lub_r.
Definition Zmax_lub := max_lub.
Definition Zmax_lub_iff := max_lub_iff.
Definition Zmax_lub_lt := max_lub_lt.
Definition Zmax_lub_lt_iff := max_lub_lt_iff.
Definition Zmax_le_compat_l := max_le_compat_l.
Definition Zmax_le_compat_r := max_le_compat_r.
Definition Zmax_le_compat := max_le_compat.

Definition Zmin_spec_le := min_spec_le.
Definition Zmin_dec := min_dec.
Definition Zmin_unicity := min_unicity.
Definition Zmin_unicity_ext := min_unicity_ext.
Definition Zmin_id := min_id.
Notation Zmin_idempotent := Zmin_id (only parsing).
Definition Zmin_assoc := min_assoc.
Definition Zmin_comm := min_comm.
Definition Zmin_l := min_l.
Definition Zmin_r := min_r.
Definition Zle_min_l := le_min_l.
Definition Zle_min_r := le_min_r.
Definition Zmin_le := min_le.
Definition Zmin_le_iff := min_le_iff.
Definition Zmin_lt_iff := min_lt_iff.
Definition Zmin_glb_l := min_glb_l.
Definition Zmin_glb_r := min_glb_r.
Definition Zmin_glb := min_glb.
Definition Zmin_glb_iff := min_glb_iff.
Definition Zmin_glb_lt := min_glb_lt.
Definition Zmin_glb_lt_iff := min_glb_lt_iff.
Definition Zmin_le_compat_l := min_le_compat_l.
Definition Zmin_le_compat_r := min_le_compat_r.
Definition Zmin_le_compat := min_le_compat.

Definition Zmin_max_absorption := min_max_absorption.
Definition Zmax_min_absorption := max_min_absorption.
Definition Zmax_min_distr := max_min_distr.
Definition Zmin_max_distr := min_max_distr.
Definition Zmax_min_modular := max_min_modular.
Definition Zmin_max_modular := min_max_modular.
Definition Zmax_min_disassoc := max_min_disassoc.


(** * Properties specific to the [Z] domain *)

(** Compatibilities (consequences of monotonicity) *)

Lemma Zplus_max_distr_l : forall n m p, Zmax (p + n) (p + m) = p + Zmax n m.
Proof.
 intros. apply Zmax_monotone.
 intros x y. apply Zplus_le_compat_l.
Qed.

Lemma Zplus_max_distr_r : forall n m p, Zmax (n + p) (m + p) = Zmax n m + p.
Proof.
 intros. rewrite (Zplus_comm n p), (Zplus_comm m p), (Zplus_comm _ p).
 apply Zplus_max_distr_l.
Qed.

Lemma Zplus_min_distr_l : forall n m p, Zmin (p + n) (p + m) = p + Zmin n m.
Proof.
 intros. apply Zmin_monotone.
 intros x y. apply Zplus_le_compat_l.
Qed.

Lemma Zplus_min_distr_r : forall n m p, Zmin (n + p) (m + p) = Zmin n m + p.
Proof.
 intros. rewrite (Zplus_comm n p), (Zplus_comm m p), (Zplus_comm _ p).
 apply Zplus_min_distr_l.
Qed.

Lemma Zsucc_max_distr : forall n m, Zsucc (Zmax n m) = Zmax (Zsucc n) (Zsucc m).
Proof.
 unfold Zsucc. intros. symmetry. apply Zplus_max_distr_r.
Qed.

Lemma Zsucc_min_distr : forall n m, Zsucc (Zmin n m) = Zmin (Zsucc n) (Zsucc m).
Proof.
 unfold Zsucc. intros. symmetry. apply Zplus_min_distr_r.
Qed.

Lemma Zpred_max_distr : forall n m, Zpred (Zmax n m) = Zmax (Zpred n) (Zpred m).
Proof.
 unfold Zpred. intros. symmetry. apply Zplus_max_distr_r.
Qed.

Lemma Zpred_min_distr : forall n m, Zsucc (Zmin n m) = Zmin (Zsucc n) (Zsucc m).
Proof.
 unfold Zpred. intros. symmetry. apply Zplus_min_distr_r.
Qed.

(** Anti-monotonicity swaps the role of [min] and [max] *)

Lemma Zopp_max_distr : forall n m : Z, -(Zmax n m) = Zmin (- n) (- m).
Proof.
 intros. symmetry. apply Zmin_max_antimonotone.
 intros x x'. rewrite Zge_iff_le; red; rewrite <- Zcompare_opp; auto.
Qed.

Lemma Zopp_min_distr : forall n m : Z, - (Zmin n m) = Zmax (- n) (- m).
Proof.
 intros. symmetry. apply Zmax_min_antimonotone.
 intros x x'. rewrite Zge_iff_le; red; rewrite <- Zcompare_opp; auto.
Qed.

Lemma Zminus_max_distr_l : forall n m p, Zmax (p - n) (p - m) = p - Zmin n m.
Proof.
 unfold Zminus. intros. rewrite Zopp_min_distr. apply Zplus_max_distr_l.
Qed.

Lemma Zminus_max_distr_r : forall n m p, Zmax (n - p) (m - p) = Zmax n m - p.
Proof.
 unfold Zminus. intros. apply Zplus_max_distr_r.
Qed.

Lemma Zminus_min_distr_l : forall n m p, Zmin (p - n) (p - m) = p - Zmax n m.
Proof.
 unfold Zminus. intros. rewrite Zopp_max_distr. apply Zplus_min_distr_l.
Qed.

Lemma Zminus_min_distr_r : forall n m p, Zmin (n - p) (m - p) = Zmin n m - p.
Proof.
 unfold Zminus. intros. apply Zplus_min_distr_r.
Qed.

(** Compatibility with [Zpos] *)

Lemma Zpos_max : forall p q, Zpos (Pmax p q) = Zmax (Zpos p) (Zpos q).
Proof.
 intros; unfold Zmax, Pmax; simpl; generalize (Pcompare_Eq_eq p q).
 destruct Pcompare; auto.
 intro H; rewrite H; auto.
Qed.

Lemma Zpos_min : forall p q, Zpos (Pmin p q) = Zmin (Zpos p) (Zpos q).
Proof.
 intros; unfold Zmin, Pmin; simpl; generalize (Pcompare_Eq_eq p q).
 destruct Pcompare; auto.
Qed.

Lemma Zpos_max_1 : forall p, Zmax 1 (Zpos p) = Zpos p.
Proof.
  intros; unfold Zmax; simpl; destruct p; simpl; auto.
Qed.

Lemma Zpos_min_1 : forall p, Zmin 1 (Zpos p) = 1.
Proof.
  intros; unfold Zmax; simpl; destruct p; simpl; auto.
Qed.


(** * Characterization of Pminus in term of Zminus and Zmax *)

Lemma Zpos_minus : forall p q, Zpos (Pminus p q) = Zmax 1 (Zpos p - Zpos q).
Proof.
  intros; simpl. destruct (Pcompare p q Eq) as [ ]_eqn:H.
  rewrite (Pcompare_Eq_eq _ _ H).
  unfold Pminus; rewrite Pminus_mask_diag; reflexivity.
  rewrite Pminus_Lt; auto.
  symmetry. apply Zpos_max_1.
Qed.


(*begin hide*)
(* Compatibility with names of the old Zminmax file *)
Notation Zmin_max_absorption_r_r := Zmin_max_absorption (only parsing).
Notation Zmax_min_absorption_r_r := Zmax_min_absorption (only parsing).
Notation Zmax_min_distr_r := Zmax_min_distr (only parsing).
Notation Zmin_max_distr_r := Zmin_max_distr (only parsing).
Notation Zmax_min_modular_r := Zmax_min_modular (only parsing).
Notation Zmin_max_modular_r := Zmin_max_modular (only parsing).
Notation max_min_disassoc := Zmax_min_disassoc (only parsing).
(*end hide*)
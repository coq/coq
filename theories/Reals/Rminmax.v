(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import OrderedType2 Rbase Rbasic_fun ROrderedType GenericMinMax.

(** * Maximum and Minimum of two real numbers *)

Local Open Scope R_scope.

(** The functions [Rmax] and [Rmin] implement indeed
    a maximum and a minimum *)

Lemma Rmax_spec : forall x y,
  (x<y /\ Rmax x y = y)  \/  (y<=x /\ Rmax x y = x).
Proof.
 unfold Rmax. intros.
 destruct Rle_dec as [H|H]; [| apply Rnot_le_lt in H ];
  unfold Rle in *; intuition.
Qed.

Lemma Rmin_spec : forall x y,
  (x<y /\ Rmin x y = x)  \/  (y<=x /\ Rmin x y = y).
Proof.
 unfold Rmin. intros.
 destruct Rle_dec as [H|H]; [| apply Rnot_le_lt in H ];
  unfold Rle in *; intuition.
Qed.

Module RHasMinMax <: HasMinMax R_as_OT.
 Definition max := Rmax.
 Definition min := Rmin.
 Definition max_spec := Rmax_spec.
 Definition min_spec := Rmin_spec.
End RHasMinMax.

(** We obtain hence all the generic properties of max and min. *)

Module Import RMinMaxProps := MinMaxProperties R_as_OT RHasMinMax.

(** For some generic properties, we can have nicer statements here,
    since underlying equality is Leibniz. *)

Lemma Rmax_case_strong : forall n m (P:R -> Type),
  (m<=n -> P n) -> (n<=m -> P m) -> P (Rmax n m).
Proof. intros; apply max_case_strong; auto. congruence. Defined.

Lemma Rmax_case : forall n m (P:R -> Type),
  P n -> P m -> P (Rmax n m).
Proof. intros. apply Rmax_case_strong; auto. Defined.

Lemma Rmax_monotone: forall f,
 (Proper (Rle ==> Rle) f) ->
 forall x y, Rmax (f x) (f y) = f (Rmax x y).
Proof. intros; apply max_monotone; auto. congruence. Qed.

Lemma Rmin_case_strong : forall n m (P:R -> Type),
  (m<=n -> P m) -> (n<=m -> P n) -> P (Rmin n m).
Proof. intros; apply min_case_strong; auto. congruence. Defined.

Lemma Rmin_case : forall n m (P:R -> Type),
  P n -> P m -> P (Rmin n m).
Proof. intros. apply Rmin_case_strong; auto. Defined.

Lemma Rmin_monotone: forall f,
 (Proper (Rle ==> Rle) f) ->
 forall x y, Rmin (f x) (f y) = f (Rmin x y).
Proof. intros; apply min_monotone; auto. congruence. Qed.

Lemma Rmax_min_antimonotone : forall f,
 Proper (Rle==>Rge) f ->
 forall x y, Rmax (f x) (f y) == f (Rmin x y).
Proof.
 intros. apply max_min_antimonotone. congruence.
 intros z z' Hz; red; apply Rge_le; auto.
Qed.

Lemma Rmin_max_antimonotone : forall f,
 Proper (Rle==>Rge) f ->
 forall x y, Rmin (f x) (f y) == f (Rmax x y).
Proof.
 intros. apply min_max_antimonotone. congruence.
 intros z z' Hz; red. apply Rge_le. auto.
Qed.

(** For the other generic properties, we make aliases,
   since otherwise SearchAbout misses some of them
   (bad interaction with an Include).
   See GenericMinMax (or SearchAbout) for the statements. *)

Definition Rmax_spec_le := max_spec_le.
Definition Rmax_dec := max_dec.
Definition Rmax_unicity := max_unicity.
Definition Rmax_unicity_ext := max_unicity_ext.
Definition Rmax_id := max_id.
Notation Rmax_idempotent := Rmax_id (only parsing).
Definition Rmax_assoc := max_assoc.
Definition Rmax_comm := max_comm.
Definition Rmax_l := max_l.
Definition Rmax_r := max_r.
Definition Zle_max_l := le_max_l.
Definition Zle_max_r := le_max_r.
Definition Rmax_le := max_le.
Definition Rmax_le_iff := max_le_iff.
Definition Rmax_lt_iff := max_lt_iff.
Definition Rmax_lub_l := max_lub_l.
Definition Rmax_lub_r := max_lub_r.
Definition Rmax_lub := max_lub.
Definition Rmax_lub_iff := max_lub_iff.
Definition Rmax_lub_lt := max_lub_lt.
Definition Rmax_lub_lt_iff := max_lub_lt_iff.
Definition Rmax_le_compat_l := max_le_compat_l.
Definition Rmax_le_compat_r := max_le_compat_r.
Definition Rmax_le_compat := max_le_compat.

Definition Rmin_spec_le := min_spec_le.
Definition Rmin_dec := min_dec.
Definition Rmin_unicity := min_unicity.
Definition Rmin_unicity_ext := min_unicity_ext.
Definition Rmin_id := min_id.
Notation Rmin_idempotent := Rmin_id (only parsing).
Definition Rmin_assoc := min_assoc.
Definition Rmin_comm := min_comm.
Definition Rmin_l := min_l.
Definition Rmin_r := min_r.
Definition Zle_min_l := le_min_l.
Definition Zle_min_r := le_min_r.
Definition Rmin_le := min_le.
Definition Rmin_le_iff := min_le_iff.
Definition Rmin_lt_iff := min_lt_iff.
Definition Rmin_glb_l := min_glb_l.
Definition Rmin_glb_r := min_glb_r.
Definition Rmin_glb := min_glb.
Definition Rmin_glb_iff := min_glb_iff.
Definition Rmin_glb_lt := min_glb_lt.
Definition Rmin_glb_lt_iff := min_glb_lt_iff.
Definition Rmin_le_compat_l := min_le_compat_l.
Definition Rmin_le_compat_r := min_le_compat_r.
Definition Rmin_le_compat := min_le_compat.

Definition Rmin_max_absorption := min_max_absorption.
Definition Rmax_min_absorption := max_min_absorption.
Definition Rmax_min_distr := max_min_distr.
Definition Rmin_max_distr := min_max_distr.
Definition Rmax_min_modular := max_min_modular.
Definition Rmin_max_modular := min_max_modular.
Definition Rmax_min_disassoc := max_min_disassoc.


(** * Properties specific to the [R] domain *)

(** Compatibilities (consequences of monotonicity) *)

Lemma Rplus_max_distr_l : forall n m p, Rmax (p + n) (p + m) = p + Rmax n m.
Proof.
 intros. apply Rmax_monotone.
 intros x y. apply Rplus_le_compat_l.
Qed.

Lemma Rplus_max_distr_r : forall n m p, Rmax (n + p) (m + p) = Rmax n m + p.
Proof.
 intros. rewrite (Rplus_comm n p), (Rplus_comm m p), (Rplus_comm _ p).
 apply Rplus_max_distr_l.
Qed.

Lemma Rplus_min_distr_l : forall n m p, Rmin (p + n) (p + m) = p + Rmin n m.
Proof.
 intros. apply Rmin_monotone.
 intros x y. apply Rplus_le_compat_l.
Qed.

Lemma Rplus_min_distr_r : forall n m p, Rmin (n + p) (m + p) = Rmin n m + p.
Proof.
 intros. rewrite (Rplus_comm n p), (Rplus_comm m p), (Rplus_comm _ p).
 apply Rplus_min_distr_l.
Qed.

(** Anti-monotonicity swaps the role of [min] and [max] *)

Lemma Ropp_max_distr : forall n m : R, -(Rmax n m) = Rmin (- n) (- m).
Proof.
 intros. symmetry. apply Rmin_max_antimonotone.
 exact Ropp_le_ge_contravar.
Qed.

Lemma Ropp_min_distr : forall n m : R, - (Rmin n m) = Rmax (- n) (- m).
Proof.
 intros. symmetry. apply Rmax_min_antimonotone.
 exact Ropp_le_ge_contravar.
Qed.

Lemma Rminus_max_distr_l : forall n m p, Rmax (p - n) (p - m) = p - Rmin n m.
Proof.
 unfold Rminus. intros. rewrite Ropp_min_distr. apply Rplus_max_distr_l.
Qed.

Lemma Rminus_max_distr_r : forall n m p, Rmax (n - p) (m - p) = Rmax n m - p.
Proof.
 unfold Rminus. intros. apply Rplus_max_distr_r.
Qed.

Lemma Rminus_min_distr_l : forall n m p, Rmin (p - n) (p - m) = p - Rmax n m.
Proof.
 unfold Rminus. intros. rewrite Ropp_max_distr. apply Rplus_min_distr_l.
Qed.

Lemma Rminus_min_distr_r : forall n m p, Rmin (n - p) (m - p) = Rmin n m - p.
Proof.
 unfold Rminus. intros. apply Rplus_min_distr_r.
Qed.

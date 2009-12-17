(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import OrderedType2 BinNat Nnat NOrderedType GenericMinMax.

(** * Maximum and Minimum of two [N] numbers *)

Local Open Scope N_scope.

(** The functions [Nmax] and [Nmin] implement indeed
    a maximum and a minimum *)

Lemma Nmax_spec : forall x y,
  (x<y /\ Nmax x y = y)  \/  (y<=x /\ Nmax x y = x).
Proof.
 unfold Nlt, Nle, Nmax. intros.
 generalize (Ncompare_eq_correct x y).
 rewrite <- (Ncompare_antisym x y).
 destruct (x ?= y); simpl; auto; right; intuition; discriminate.
Qed.

Lemma Nmin_spec : forall x y,
  (x<y /\ Nmin x y = x)  \/  (y<=x /\ Nmin x y = y).
Proof.
 unfold Nlt, Nle, Nmin. intros.
 generalize (Ncompare_eq_correct x y).
 rewrite <- (Ncompare_antisym x y).
 destruct (x ?= y); simpl; auto; right; intuition; discriminate.
Qed.

Module NHasMinMax <: HasMinMax N_as_OT.
 Definition max := Nmax.
 Definition min := Nmin.
 Definition max_spec := Nmax_spec.
 Definition min_spec := Nmin_spec.
End NHasMinMax.

(** We obtain hence all the generic properties of max and min. *)

Module Import NMinMaxProps := MinMaxProperties N_as_OT NHasMinMax.

(** For some generic properties, we can have nicer statements here,
    since underlying equality is Leibniz. *)

Lemma Nmax_case_strong : forall n m (P:N -> Type),
  (m<=n -> P n) -> (n<=m -> P m) -> P (Nmax n m).
Proof. intros; apply max_case_strong; auto. congruence. Defined.

Lemma Nmax_case : forall n m (P:N -> Type),
  P n -> P m -> P (Nmax n m).
Proof. intros. apply Nmax_case_strong; auto. Defined.

Lemma Nmax_monotone: forall f,
 (Proper (Nle ==> Nle) f) ->
 forall x y, Nmax (f x) (f y) = f (Nmax x y).
Proof. intros; apply max_monotone; auto. congruence. Qed.

Lemma Nmin_case_strong : forall n m (P:N -> Type),
  (n<=m -> P n) -> (m<=n -> P m) -> P (Nmin n m).
Proof. intros; apply min_case_strong; auto. congruence. Defined.

Lemma Nmin_case : forall n m (P:N -> Type),
  P n -> P m -> P (Nmin n m).
Proof. intros. apply Nmin_case_strong; auto. Defined.

Lemma Nmin_monotone: forall f,
 (Proper (Nle ==> Nle) f) ->
 forall x y, Nmin (f x) (f y) = f (Nmin x y).
Proof. intros; apply min_monotone; auto. congruence. Qed.

Lemma Nmax_min_antimonotone : forall f,
 Proper (Nle==>Nge) f ->
 forall x y, Nmax (f x) (f y) == f (Nmin x y).
Proof.
 intros f H. apply max_min_antimonotone. congruence.
 intros x x' Hx. red. specialize (H _ _ Hx). clear Hx.
 unfold Nle, Nge in *; contradict H. rewrite <- Ncompare_antisym, H; auto.
Qed.

Lemma Nmin_max_antimonotone : forall f,
 Proper (Nle==>Nge) f ->
 forall x y, Nmin (f x) (f y) == f (Nmax x y).
Proof.
 intros f H. apply min_max_antimonotone. congruence.
 intros z z' Hz; red. specialize (H _ _ Hz). clear Hz.
 unfold Nle, Nge in *. contradict H. rewrite <- Ncompare_antisym, H; auto.
Qed.

(** For the other generic properties, we make aliases,
   since otherwise SearchAbout misses some of them
   (bad interaction with an Include).
   See GenericMinMax (or SearchAbout) for the statements. *)

Definition Nmax_spec_le := max_spec_le.
Definition Nmax_dec := max_dec.
Definition Nmax_unicity := max_unicity.
Definition Nmax_unicity_ext := max_unicity_ext.
Definition Nmax_id := max_id.
Notation Nmax_idempotent := Nmax_id (only parsing).
Definition Nmax_assoc := max_assoc.
Definition Nmax_comm := max_comm.
Definition Nmax_l := max_l.
Definition Nmax_r := max_r.
Definition Nle_max_l := le_max_l.
Definition Nle_max_r := le_max_r.
Definition Nmax_le := max_le.
Definition Nmax_le_iff := max_le_iff.
Definition Nmax_lt_iff := max_lt_iff.
Definition Nmax_lub_l := max_lub_l.
Definition Nmax_lub_r := max_lub_r.
Definition Nmax_lub := max_lub.
Definition Nmax_lub_iff := max_lub_iff.
Definition Nmax_lub_lt := max_lub_lt.
Definition Nmax_lub_lt_iff := max_lub_lt_iff.
Definition Nmax_le_compat_l := max_le_compat_l.
Definition Nmax_le_compat_r := max_le_compat_r.
Definition Nmax_le_compat := max_le_compat.

Definition Nmin_spec_le := min_spec_le.
Definition Nmin_dec := min_dec.
Definition Nmin_unicity := min_unicity.
Definition Nmin_unicity_ext := min_unicity_ext.
Definition Nmin_id := min_id.
Notation Nmin_idempotent := Nmin_id (only parsing).
Definition Nmin_assoc := min_assoc.
Definition Nmin_comm := min_comm.
Definition Nmin_l := min_l.
Definition Nmin_r := min_r.
Definition Nle_min_l := le_min_l.
Definition Nle_min_r := le_min_r.
Definition Nmin_le := min_le.
Definition Nmin_le_iff := min_le_iff.
Definition Nmin_lt_iff := min_lt_iff.
Definition Nmin_glb_l := min_glb_l.
Definition Nmin_glb_r := min_glb_r.
Definition Nmin_glb := min_glb.
Definition Nmin_glb_iff := min_glb_iff.
Definition Nmin_glb_lt := min_glb_lt.
Definition Nmin_glb_lt_iff := min_glb_lt_iff.
Definition Nmin_le_compat_l := min_le_compat_l.
Definition Nmin_le_compat_r := min_le_compat_r.
Definition Nmin_le_compat := min_le_compat.

Definition Nmin_max_absorption := min_max_absorption.
Definition Nmax_min_absorption := max_min_absorption.
Definition Nmax_min_distr := max_min_distr.
Definition Nmin_max_distr := min_max_distr.
Definition Nmax_min_modular := max_min_modular.
Definition Nmin_max_modular := min_max_modular.
Definition Nmax_min_disassoc := max_min_disassoc.



(** * Properties specific to the [positive] domain *)

(** Simplifications *)

Lemma Nmax_0_l : forall n, Nmax 0 n = n.
Proof.
 intros. unfold Nmax. rewrite <- Ncompare_antisym. generalize (Ncompare_0 n).
 destruct (n ?= 0); intuition.
Qed.

Lemma Nmax_0_r : forall n, Nmax n 0 = n.
Proof. intros. rewrite max_comm. apply Nmax_0_l. Qed.

Lemma Nmin_0_l : forall n, Nmin 0 n = 0.
Proof.
 intros. unfold Nmin. rewrite <- Ncompare_antisym. generalize (Ncompare_0 n).
 destruct (n ?= 0); intuition.
Qed.

Lemma Nmin_0_r : forall n, Nmin n 0 = 0.
Proof. intros. rewrite min_comm. apply Nmin_0_l. Qed.

(** Compatibilities (consequences of monotonicity) *)

Lemma Nsucc_max_distr :
 forall n m, Nsucc (Nmax n m) = Nmax (Nsucc n) (Nsucc m).
Proof.
 intros. symmetry. apply Nmax_monotone.
 intros x x'. unfold Nle.
 rewrite 2 nat_of_Ncompare, 2 nat_of_Nsucc.
 simpl; auto.
Qed.

Lemma Nsucc_min_distr : forall n m, Nsucc (Nmin n m) = Nmin (Nsucc n) (Nsucc m).
Proof.
 intros. symmetry. apply Nmin_monotone.
 intros x x'. unfold Nle.
 rewrite 2 nat_of_Ncompare, 2 nat_of_Nsucc.
 simpl; auto.
Qed.

Lemma Nplus_max_distr_l : forall n m p, Nmax (p + n) (p + m) = p + Nmax n m.
Proof.
 intros. apply Nmax_monotone.
 intros x x'. unfold Nle.
 rewrite 2 nat_of_Ncompare, 2 nat_of_Nplus.
 rewrite <- 2 Compare_dec.nat_compare_le. auto with arith.
Qed.

Lemma Nplus_max_distr_r : forall n m p, Nmax (n + p) (m + p) = Nmax n m + p.
Proof.
 intros. rewrite (Nplus_comm n p), (Nplus_comm m p), (Nplus_comm _ p).
 apply Nplus_max_distr_l.
Qed.

Lemma Nplus_min_distr_l : forall n m p, Nmin (p + n) (p + m) = p + Nmin n m.
Proof.
 intros. apply Nmin_monotone.
 intros x x'. unfold Nle.
 rewrite 2 nat_of_Ncompare, 2 nat_of_Nplus.
 rewrite <- 2 Compare_dec.nat_compare_le. auto with arith.
Qed.

Lemma Nplus_min_distr_r : forall n m p, Nmin (n + p) (m + p) = Nmin n m + p.
Proof.
 intros. rewrite (Nplus_comm n p), (Nplus_comm m p), (Nplus_comm _ p).
 apply Nplus_min_distr_l.
Qed.

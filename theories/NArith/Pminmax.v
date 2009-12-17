(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import OrderedType2 BinPos Pnat POrderedType GenericMinMax.

(** * Maximum and Minimum of two positive numbers *)

Local Open Scope positive_scope.

(** The functions [Pmax] and [Pmin] implement indeed
    a maximum and a minimum *)

Lemma Pmax_spec : forall x y,
  (x<y /\ Pmax x y = y)  \/  (y<=x /\ Pmax x y = x).
Proof.
 unfold Plt, Ple, Pmax. intros.
 generalize (Pcompare_eq_iff x y). rewrite (ZC4 y x).
 destruct ((x ?= y) Eq); simpl; auto; right; intuition; discriminate.
Qed.

Lemma Pmin_spec : forall x y,
  (x<y /\ Pmin x y = x)  \/  (y<=x /\ Pmin x y = y).
Proof.
 unfold Plt, Ple, Pmin. intros.
 generalize (Pcompare_eq_iff x y). rewrite (ZC4 y x).
 destruct ((x ?= y) Eq); simpl; auto; right; intuition; discriminate.
Qed.

Module PositiveHasMinMax <: HasMinMax Positive_as_OT.
 Definition max := Pmax.
 Definition min := Pmin.
 Definition max_spec := Pmax_spec.
 Definition min_spec := Pmin_spec.
End PositiveHasMinMax.

(** We obtain hence all the generic properties of max and min. *)

Module Import NatMinMaxProps :=
 MinMaxProperties Positive_as_OT PositiveHasMinMax.


(** For some generic properties, we can have nicer statements here,
    since underlying equality is Leibniz. *)

Lemma Pmax_case_strong : forall n m (P:positive -> Type),
  (m<=n -> P n) -> (n<=m -> P m) -> P (Pmax n m).
Proof. intros; apply max_case_strong; auto. congruence. Defined.

Lemma Pmax_case : forall n m (P:positive -> Type),
  P n -> P m -> P (Pmax n m).
Proof. intros. apply Pmax_case_strong; auto. Defined.

Lemma Pmax_monotone: forall f,
 (Proper (Ple ==> Ple) f) ->
 forall x y, Pmax (f x) (f y) = f (Pmax x y).
Proof. intros; apply max_monotone; auto. congruence. Qed.

Lemma Pmin_case_strong : forall n m (P:positive -> Type),
  (n<=m -> P n) -> (m<=n -> P m) -> P (Pmin n m).
Proof. intros; apply min_case_strong; auto. congruence. Defined.

Lemma Pmin_case : forall n m (P:positive -> Type),
  P n -> P m -> P (Pmin n m).
Proof. intros. apply Pmin_case_strong; auto. Defined.

Lemma Pmin_monotone: forall f,
 (Proper (Ple ==> Ple) f) ->
 forall x y, Pmin (f x) (f y) = f (Pmin x y).
Proof. intros; apply min_monotone; auto. congruence. Qed.

Lemma Pmax_min_antimonotone : forall f,
 Proper (Ple==>Pge) f ->
 forall x y, Pmax (f x) (f y) == f (Pmin x y).
Proof.
 intros f H. apply max_min_antimonotone. congruence.
 intros z z' Hz; red. specialize (H _ _ Hz). clear Hz.
 unfold Ple, Pge in *. contradict H. rewrite ZC4, H; auto.
Qed.

Lemma Pmin_max_antimonotone : forall f,
 Proper (Ple==>Pge) f ->
 forall x y, Pmin (f x) (f y) == f (Pmax x y).
Proof.
 intros f H. apply min_max_antimonotone. congruence.
 intros z z' Hz; red. specialize (H _ _ Hz). clear Hz.
 unfold Ple, Pge in *. contradict H. rewrite ZC4, H; auto.
Qed.

(** For the other generic properties, we make aliases,
   since otherwise SearchAbout misses some of them
   (bad interaction with an Include).
   See GenericMinMax (or SearchAbout) for the statements. *)

Definition Pmax_spec_le := max_spec_le.
Definition Pmax_dec := max_dec.
Definition Pmax_unicity := max_unicity.
Definition Pmax_unicity_ext := max_unicity_ext.
Definition Pmax_id := max_id.
Notation Pmax_idempotent := Pmax_id (only parsing).
Definition Pmax_assoc := max_assoc.
Definition Pmax_comm := max_comm.
Definition Pmax_l := max_l.
Definition Pmax_r := max_r.
Definition Ple_max_l := le_max_l.
Definition Ple_max_r := le_max_r.
Definition Pmax_le := max_le.
Definition Pmax_le_iff := max_le_iff.
Definition Pmax_lt_iff := max_lt_iff.
Definition Pmax_lub_l := max_lub_l.
Definition Pmax_lub_r := max_lub_r.
Definition Pmax_lub := max_lub.
Definition Pmax_lub_iff := max_lub_iff.
Definition Pmax_lub_lt := max_lub_lt.
Definition Pmax_lub_lt_iff := max_lub_lt_iff.
Definition Pmax_le_compat_l := max_le_compat_l.
Definition Pmax_le_compat_r := max_le_compat_r.
Definition Pmax_le_compat := max_le_compat.

Definition Pmin_spec_le := min_spec_le.
Definition Pmin_dec := min_dec.
Definition Pmin_unicity := min_unicity.
Definition Pmin_unicity_ext := min_unicity_ext.
Definition Pmin_id := min_id.
Notation Pmin_idempotent := Pmin_id (only parsing).
Definition Pmin_assoc := min_assoc.
Definition Pmin_comm := min_comm.
Definition Pmin_l := min_l.
Definition Pmin_r := min_r.
Definition Ple_min_l := le_min_l.
Definition Ple_min_r := le_min_r.
Definition Pmin_le := min_le.
Definition Pmin_le_iff := min_le_iff.
Definition Pmin_lt_iff := min_lt_iff.
Definition Pmin_glb_l := min_glb_l.
Definition Pmin_glb_r := min_glb_r.
Definition Pmin_glb := min_glb.
Definition Pmin_glb_iff := min_glb_iff.
Definition Pmin_glb_lt := min_glb_lt.
Definition Pmin_glb_lt_iff := min_glb_lt_iff.
Definition Pmin_le_compat_l := min_le_compat_l.
Definition Pmin_le_compat_r := min_le_compat_r.
Definition Pmin_le_compat := min_le_compat.

Definition Pmin_max_absorption := min_max_absorption.
Definition Pmax_min_absorption := max_min_absorption.
Definition Pmax_min_distr := max_min_distr.
Definition Pmin_max_distr := min_max_distr.
Definition Pmax_min_modular := max_min_modular.
Definition Pmin_max_modular := min_max_modular.
Definition Pmax_min_disassoc := max_min_disassoc.


(** * Properties specific to the [positive] domain *)

(** Simplifications *)

Lemma Pmax_1_l : forall n, Pmax 1 n = n.
Proof.
 intros. unfold Pmax. rewrite ZC4. generalize (Pcompare_1 n).
 destruct (n ?= 1); intuition.
Qed.

Lemma Pmax_1_r : forall n, Pmax n 1 = n.
Proof. intros. rewrite max_comm. apply Pmax_1_l. Qed.

Lemma Pmin_1_l : forall n, Pmin 1 n = 1.
Proof.
 intros. unfold Pmin. rewrite ZC4. generalize (Pcompare_1 n).
 destruct (n ?= 1); intuition.
Qed.

Lemma Pmin_1_r : forall n, Pmin n 1 = 1.
Proof. intros. rewrite min_comm. apply Pmin_1_l. Qed.

(** Compatibilities (consequences of monotonicity) *)

Lemma Psucc_max_distr :
 forall n m, Psucc (Pmax n m) = Pmax (Psucc n) (Psucc m).
Proof.
 intros. symmetry. apply Pmax_monotone.
 intros x x'. unfold Ple.
 rewrite 2 nat_of_P_compare_morphism, 2 nat_of_P_succ_morphism.
 simpl; auto.
Qed.

Lemma Psucc_min_distr : forall n m, Psucc (Pmin n m) = Pmin (Psucc n) (Psucc m).
Proof.
 intros. symmetry. apply Pmin_monotone.
 intros x x'. unfold Ple.
 rewrite 2 nat_of_P_compare_morphism, 2 nat_of_P_succ_morphism.
 simpl; auto.
Qed.

Lemma Pplus_max_distr_l : forall n m p, Pmax (p + n) (p + m) = p + Pmax n m.
Proof.
 intros. apply Pmax_monotone.
 intros x x'. unfold Ple.
 rewrite 2 nat_of_P_compare_morphism, 2 nat_of_P_plus_morphism.
 rewrite <- 2 Compare_dec.nat_compare_le. auto with arith.
Qed.

Lemma Pplus_max_distr_r : forall n m p, Pmax (n + p) (m + p) = Pmax n m + p.
Proof.
 intros. rewrite (Pplus_comm n p), (Pplus_comm m p), (Pplus_comm _ p).
 apply Pplus_max_distr_l.
Qed.

Lemma Pplus_min_distr_l : forall n m p, Pmin (p + n) (p + m) = p + Pmin n m.
Proof.
 intros. apply Pmin_monotone.
 intros x x'. unfold Ple.
 rewrite 2 nat_of_P_compare_morphism, 2 nat_of_P_plus_morphism.
 rewrite <- 2 Compare_dec.nat_compare_le. auto with arith.
Qed.

Lemma Pplus_min_distr_r : forall n m p, Pmin (n + p) (m + p) = Pmin n m + p.
Proof.
 intros. rewrite (Pplus_comm n p), (Pplus_comm m p), (Pplus_comm _ p).
 apply Pplus_min_distr_l.
Qed.

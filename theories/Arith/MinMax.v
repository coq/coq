(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import OrderedType2 NatOrderedType GenericMinMax.

(** * Maximum and Minimum of two natural numbers *)

Fixpoint max n m : nat :=
  match n, m with
    | O, _ => m
    | S n', O => n
    | S n', S m' => S (max n' m')
  end.

Fixpoint min n m : nat :=
  match n, m with
    | O, _ => 0
    | S n', O => 0
    | S n', S m' => S (min n' m')
  end.

(** These functions implement indeed a maximum and a minimum *)

Lemma max_spec : forall x y,
  (x<y /\ max x y = y)  \/  (y<=x /\ max x y = x).
Proof.
 induction x; destruct y; simpl; auto with arith.
 destruct (IHx y); intuition.
Qed.

Lemma min_spec : forall x y,
  (x<y /\ min x y = x)  \/  (y<=x /\ min x y = y).
Proof.
 induction x; destruct y; simpl; auto with arith.
 destruct (IHx y); intuition.
Qed.

Module NatHasMinMax <: HasMinMax Nat_as_OT.
 Definition max := max.
 Definition min := min.
 Definition max_spec := max_spec.
 Definition min_spec := min_spec.
End NatHasMinMax.

(** We obtain hence all the generic properties of max and min. *)

Module Import NatMinMaxProps := MinMaxProperties Nat_as_OT NatHasMinMax.

(** For some generic properties, we can have nicer statements here,
    since underlying equality is Leibniz. *)

Lemma max_case_strong : forall n m (P:nat -> Type),
  (m<=n -> P n) -> (n<=m -> P m) -> P (max n m).
Proof. intros; apply max_case_strong; auto. congruence. Defined.

Lemma max_case : forall n m (P:nat -> Type),
  P n -> P m -> P (max n m).
Proof. intros. apply max_case_strong; auto. Defined.

Lemma max_monotone: forall f,
 (Proper (le ==> le) f) ->
 forall x y, max (f x) (f y) = f (max x y).
Proof. intros; apply max_monotone; auto. congruence. Qed.

Lemma min_case_strong : forall n m (P:nat -> Type),
  (m<=n -> P m) -> (n<=m -> P n) -> P (min n m).
Proof. intros; apply min_case_strong; auto. congruence. Defined.

Lemma min_case : forall n m (P:nat -> Type),
  P n -> P m -> P (min n m).
Proof. intros. apply min_case_strong; auto. Defined.

Lemma min_monotone: forall f,
 (Proper (le ==> le) f) ->
 forall x y, min (f x) (f y) = f (min x y).
Proof. intros; apply min_monotone; auto. congruence. Qed.

Lemma max_min_antimonotone : forall f,
 Proper (le==>ge) f ->
 forall x y, max (f x) (f y) == f (min x y).
Proof.
 intros. apply max_min_antimonotone. congruence.
 intros z z' Hz; red; unfold ge in *; auto.
Qed.

Lemma min_max_antimonotone : forall f,
 Proper (le==>ge) f ->
 forall x y, min (f x) (f y) == f (max x y).
Proof.
 intros. apply min_max_antimonotone. congruence.
 intros z z' Hz; red; unfold ge in *; auto.
Qed.

(** For the other generic properties, we make aliases,
   since otherwise SearchAbout misses some of them
   (bad interaction with an Include).
   See GenericMinMax (or SearchAbout) for the statements. *)

Definition max_spec_le := max_spec_le.
Definition max_dec := max_dec.
Definition max_unicity := max_unicity.
Definition max_unicity_ext := max_unicity_ext.
Definition max_id := max_id.
Notation max_idempotent := max_id (only parsing).
Definition max_assoc := max_assoc.
Definition max_comm := max_comm.
Definition max_l := max_l.
Definition max_r := max_r.
Definition le_max_l := le_max_l.
Definition le_max_r := le_max_r.
Definition max_le := max_le.
Definition max_le_iff := max_le_iff.
Definition max_lt_iff := max_lt_iff.
Definition max_lub_l := max_lub_l.
Definition max_lub_r := max_lub_r.
Definition max_lub := max_lub.
Definition max_lub_iff := max_lub_iff.
Definition max_lub_lt := max_lub_lt.
Definition max_lub_lt_iff := max_lub_lt_iff.
Definition max_le_compat_l := max_le_compat_l.
Definition max_le_compat_r := max_le_compat_r.
Definition max_le_compat := max_le_compat.

Definition min_spec_le := min_spec_le.
Definition min_dec := min_dec.
Definition min_unicity := min_unicity.
Definition min_unicity_ext := min_unicity_ext.
Definition min_id := min_id.
Notation min_idempotent := min_id (only parsing).
Definition min_assoc := min_assoc.
Definition min_comm := min_comm.
Definition min_l := min_l.
Definition min_r := min_r.
Definition le_min_l := le_min_l.
Definition le_min_r := le_min_r.
Definition min_le := min_le.
Definition min_le_iff := min_le_iff.
Definition min_lt_iff := min_lt_iff.
Definition min_glb_l := min_glb_l.
Definition min_glb_r := min_glb_r.
Definition min_glb := min_glb.
Definition min_glb_iff := min_glb_iff.
Definition min_glb_lt := min_glb_lt.
Definition min_glb_lt_iff := min_glb_lt_iff.
Definition min_le_compat_l := min_le_compat_l.
Definition min_le_compat_r := min_le_compat_r.
Definition min_le_compat := min_le_compat.

Definition min_max_absorption := min_max_absorption.
Definition max_min_absorption := max_min_absorption.
Definition max_min_distr := max_min_distr.
Definition min_max_distr := min_max_distr.
Definition max_min_modular := max_min_modular.
Definition min_max_modular := min_max_modular.
Definition max_min_disassoc := max_min_disassoc.


(** * Properties specific to the [nat] domain *)

(** Simplifications *)

Lemma max_0_l : forall n, max 0 n = n.
Proof. reflexivity. Qed.

Lemma max_0_r : forall n, max n 0 = n.
Proof. destruct n; auto. Qed.

Lemma min_0_l : forall n, min 0 n = 0.
Proof. reflexivity. Qed.

Lemma min_0_r : forall n, min n 0 = 0.
Proof. destruct n; auto. Qed.

(** Compatibilities (consequences of monotonicity) *)

Lemma succ_max_distr : forall n m, S (max n m) = max (S n) (S m).
Proof. auto. Qed.

Lemma succ_min_distr : forall n m, S (min n m) = min (S n) (S m).
Proof. auto. Qed.

Lemma plus_max_distr_l : forall n m p, max (p + n) (p + m) = p + max n m.
Proof.
intros. apply max_monotone. repeat red; auto with arith.
Qed.

Lemma plus_max_distr_r : forall n m p, max (n + p) (m + p) = max n m + p.
Proof.
intros. apply max_monotone with (f:=fun x => x + p).
repeat red; auto with arith.
Qed.

Lemma plus_min_distr_l : forall n m p, min (p + n) (p + m) = p + min n m.
Proof.
intros. apply min_monotone. repeat red; auto with arith.
Qed.

Lemma plus_min_distr_r : forall n m p, min (n + p) (m + p) = min n m + p.
Proof.
intros. apply min_monotone with (f:=fun x => x + p).
repeat red; auto with arith.
Qed.

Hint Resolve
 max_l max_r le_max_l le_max_r
 min_l min_r le_min_l le_min_r : arith v62.

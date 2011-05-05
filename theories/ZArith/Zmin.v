(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(** THIS FILE IS DEPRECATED. Use [ZBinary.Z] instead. *)

Require Import BinInt Zcompare Zorder ZBinary.

Open Local Scope Z_scope.

(** Definition [Zmin] is now [BinInt.Zmin]. *)

(** * Characterization of the minimum on binary integer numbers *)

Definition Zmin_case := Z.min_case.
Definition Zmin_case_strong := Z.min_case_strong.

Lemma Zmin_spec : forall x y,
  x <= y /\ Zmin x y = x  \/  x > y /\ Zmin x y = y.
Proof.
 intros x y. rewrite Zgt_iff_lt, Z.min_comm. destruct (Z.min_spec y x); auto.
Qed.

(** * Greatest lower bound properties of min *)

Definition Zle_min_l : forall n m, Zmin n m <= n := Z.le_min_l.
Definition Zle_min_r : forall n m, Zmin n m <= m := Z.le_min_r.

Definition Zmin_glb : forall n m p, p <= n -> p <= m -> p <= Zmin n m
 := Z.min_glb.
Definition Zmin_glb_lt : forall n m p, p < n -> p < m -> p < Zmin n m
 := Z.min_glb_lt.

(** * Compatibility with order *)

Definition Zle_min_compat_r : forall n m p, n <= m -> Zmin n p <= Zmin m p
 := Z.min_le_compat_r.
Definition Zle_min_compat_l : forall n m p, n <= m -> Zmin p n <= Zmin p m
 := Z.min_le_compat_l.

(** * Semi-lattice properties of min *)

Definition Zmin_idempotent : forall n, Zmin n n = n := Z.min_id.
Notation Zmin_n_n := Zmin_idempotent (only parsing).
Definition Zmin_comm : forall n m, Zmin n m = Zmin m n := Z.min_comm.
Definition Zmin_assoc : forall n m p, Zmin n (Zmin m p) = Zmin (Zmin n m) p
 := Z.min_assoc.

(** * Additional properties of min *)

Lemma Zmin_irreducible_inf : forall n m, {Zmin n m = n} + {Zmin n m = m}.
Proof. exact Z.min_dec. Qed.

Lemma Zmin_irreducible : forall n m, Zmin n m = n \/ Zmin n m = m.
Proof. intros; destruct (Z.min_dec n m); auto. Qed.

Notation Zmin_or := Zmin_irreducible (only parsing).

Lemma Zmin_le_prime_inf : forall n m p, Zmin n m <= p -> {n <= p} + {m <= p}.
Proof. intros n m p; apply Zmin_case; auto. Qed.

(** * Operations preserving min *)

Definition Zsucc_min_distr :
 forall n m, Zsucc (Zmin n m) = Zmin (Zsucc n) (Zsucc m)
 := Z.succ_min_distr.

Notation Zmin_SS := Z.succ_min_distr (only parsing).

Definition Zplus_min_distr_r :
 forall n m p, Zmin (n + p) (m + p) = Zmin n m + p
 := Z.add_min_distr_r.

Notation Zmin_plus := Z.add_min_distr_r (only parsing).

(** * Minimum and Zpos *)

Lemma Zpos_min : forall p q, Zpos (Pmin p q) = Zmin (Zpos p) (Zpos q).
Proof.
 intros; unfold Zmin, Pmin; simpl. destruct Pos.compare; auto.
Qed.

Lemma Zpos_min_1 : forall p, Zmin 1 (Zpos p) = 1.
Proof.
  intros; unfold Zmax; simpl; destruct p; simpl; auto.
Qed.






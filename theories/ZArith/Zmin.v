(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** THIS FILE IS DEPRECATED. *)

Require Import BinInt Zcompare Zorder.

Local Open Scope Z_scope.

(** Definition [Zmin] is now [BinInt.Z.min]. *)

(** * Characterization of the minimum on binary integer numbers *)

Definition Zmin_case := Z.min_case.
Definition Zmin_case_strong := Z.min_case_strong.

Lemma Zmin_spec x y :
  x <= y /\ Z.min x y = x  \/  x > y /\ Z.min x y = y.
Proof.
 Z.swap_greater. rewrite Z.min_comm. destruct (Z.min_spec y x); auto.
Qed.

(** * Greatest lower bound properties of min *)

Lemma Zle_min_l : forall n m, Z.min n m <= n. Proof Z.le_min_l.
Lemma Zle_min_r : forall n m, Z.min n m <= m. Proof Z.le_min_r.

Lemma Zmin_glb : forall n m p, p <= n -> p <= m -> p <= Z.min n m.
Proof Z.min_glb.
Lemma Zmin_glb_lt : forall n m p, p < n -> p < m -> p < Z.min n m.
Proof Z.min_glb_lt.

(** * Compatibility with order *)

Lemma Zle_min_compat_r : forall n m p, n <= m -> Z.min n p <= Z.min m p.
Proof Z.min_le_compat_r.
Lemma Zle_min_compat_l : forall n m p, n <= m -> Z.min p n <= Z.min p m.
Proof Z.min_le_compat_l.

(** * Semi-lattice properties of min *)

Lemma Zmin_idempotent : forall n, Z.min n n = n. Proof Z.min_id.
Notation Zmin_n_n := Z.min_id (only parsing).
Lemma Zmin_comm : forall n m, Z.min n m = Z.min m n. Proof Z.min_comm.
Lemma Zmin_assoc : forall n m p, Z.min n (Z.min m p) = Z.min (Z.min n m) p.
Proof Z.min_assoc.

(** * Additional properties of min *)

Lemma Zmin_irreducible_inf : forall n m, {Z.min n m = n} + {Z.min n m = m}.
Proof Z.min_dec.

Lemma Zmin_irreducible n m : Z.min n m = n \/ Z.min n m = m.
Proof. destruct (Z.min_dec n m); auto. Qed.

Notation Zmin_or := Zmin_irreducible (only parsing).

Lemma Zmin_le_prime_inf n m p : Z.min n m <= p -> {n <= p} + {m <= p}.
Proof. apply Zmin_case; auto. Qed.

(** * Operations preserving min *)

Lemma Zsucc_min_distr :
 forall n m, Z.succ (Z.min n m) = Z.min (Z.succ n) (Z.succ m).
Proof Z.succ_min_distr.

Notation Zmin_SS := Z.succ_min_distr (only parsing).

Lemma Zplus_min_distr_r :
 forall n m p, Z.min (n + p) (m + p) = Z.min n m + p.
Proof Z.add_min_distr_r.

Notation Zmin_plus := Z.add_min_distr_r (only parsing).

(** * Minimum and Zpos *)

Lemma Zpos_min p q : Zpos (Pos.min p q) = Z.min (Zpos p) (Zpos q).
Proof.
 unfold Z.min, Pos.min; simpl. destruct Pos.compare; auto.
Qed.

Lemma Zpos_min_1 p : Z.min 1 (Zpos p) = 1.
Proof.
 now destruct p.
Qed.






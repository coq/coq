(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** THIS FILE IS DEPRECATED. *)

Require Export BinInt Zcompare Zorder.

Local Open Scope Z_scope.

(** Definition [Zmax] is now [BinInt.Z.max]. *)

(** * Characterization of maximum on binary integer numbers *)

Definition Zmax_case := Z.max_case.
Definition Zmax_case_strong := Z.max_case_strong.

Lemma Zmax_spec x y :
  x >= y /\ Z.max x y = x  \/ x < y /\ Z.max x y = y.
Proof.
 Z.swap_greater. destruct (Z.max_spec x y); auto.
Qed.

Lemma Zmax_left n m : n>=m -> Z.max n m = n.
Proof. Z.swap_greater. apply Zmax_l. Qed.

Lemma Zmax_right : forall n m, n<=m -> Z.max n m = m. Proof Zmax_r.

(** * Least upper bound properties of max *)

Lemma Zle_max_l : forall n m, n <= Z.max n m. Proof Z.le_max_l.
Lemma Zle_max_r : forall n m, m <= Z.max n m. Proof Z.le_max_r.

Lemma Zmax_lub : forall n m p, n <= p -> m <= p -> Z.max n m <= p.
Proof Z.max_lub.

Lemma Zmax_lub_lt : forall n m p:Z, n < p -> m < p -> Z.max n m < p.
Proof Z.max_lub_lt.


(** * Compatibility with order *)

Lemma Zle_max_compat_r : forall n m p, n <= m -> Z.max n p <= Z.max m p.
Proof Z.max_le_compat_r.

Lemma Zle_max_compat_l : forall n m p, n <= m -> Z.max p n <= Z.max p m.
Proof Z.max_le_compat_l.


(** * Semi-lattice properties of max *)

Lemma Zmax_idempotent : forall n, Z.max n n = n. Proof Z.max_id.
Lemma Zmax_comm : forall n m, Z.max n m = Z.max m n. Proof Z.max_comm.
Lemma Zmax_assoc : forall n m p, Z.max n (Z.max m p) = Z.max (Z.max n m) p.
Proof Z.max_assoc.

(** * Additional properties of max *)

Lemma Zmax_irreducible_dec : forall n m, {Z.max n m = n} + {Z.max n m = m}.
Proof Z.max_dec.

Lemma Zmax_le_prime : forall n m p, p <= Z.max n m -> p <= n \/ p <= m.
Proof Z.max_le.


(** * Operations preserving max *)

Lemma Zsucc_max_distr :
  forall n m, Z.succ (Z.max n m) = Z.max (Z.succ n) (Z.succ m).
Proof Z.succ_max_distr.

Lemma Zplus_max_distr_l : forall n m p, Z.max (p + n) (p + m) = p + Z.max n m.
Proof Z.add_max_distr_l.

Lemma Zplus_max_distr_r : forall n m p, Z.max (n + p) (m + p) = Z.max n m + p.
Proof Z.add_max_distr_r.

(** * Maximum and Zpos *)

Lemma Zpos_max p q : Zpos (Pos.max p q) = Z.max (Zpos p) (Zpos q).
Proof.
 unfold Zmax, Pmax. simpl.
 case Pos.compare_spec; auto; congruence.
Qed.

Lemma Zpos_max_1 p : Z.max 1 (Zpos p) = Zpos p.
Proof.
 now destruct p.
Qed.

(** * Characterization of Pos.sub in term of Z.sub and Z.max *)

Lemma Zpos_minus p q : Zpos (p - q) = Z.max 1 (Zpos p - Zpos q).
Proof.
  simpl. rewrite Z.pos_sub_spec. case Pos.compare_spec; intros H.
  subst; now rewrite Pos.sub_diag.
  now rewrite Pos.sub_lt.
  symmetry. apply Zpos_max_1.
Qed.

(* begin hide *)
(* Compatibility *)
Notation Zmax1 := Z.le_max_l (only parsing).
Notation Zmax2 := Z.le_max_r (only parsing).
Notation Zmax_irreducible_inf := Z.max_dec (only parsing).
Notation Zmax_le_prime_inf := Z.max_le (only parsing).
(* end hide *)

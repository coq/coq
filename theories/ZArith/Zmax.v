(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i $Id$ i*)

(** THIS FILE IS DEPRECATED. Use [ZBinary.Z] instead. *)

Require Export BinInt Zcompare Zorder ZBinary.

Open Local Scope Z_scope.

(** Definition [Zmax] is now [BinInt.Zmax]. *)


(** * Characterization of maximum on binary integer numbers *)

Definition Zmax_case := Z.max_case.
Definition Zmax_case_strong := Z.max_case_strong.

Lemma Zmax_spec : forall x y,
  x >= y /\ Zmax x y = x  \/ x < y /\ Zmax x y = y.
Proof.
 intros x y. rewrite Zge_iff_le. destruct (Z.max_spec x y); auto.
Qed.

Lemma Zmax_left : forall n m, n>=m -> Zmax n m = n.
Proof. intros x y. rewrite Zge_iff_le. apply Zmax_l. Qed.

Definition Zmax_right : forall n m, n<=m -> Zmax n m = m := Zmax_r.

(** * Least upper bound properties of max *)

Definition Zle_max_l : forall n m, n <= Zmax n m := Z.le_max_l.
Definition Zle_max_r : forall n m, m <= Zmax n m := Z.le_max_r.

Definition Zmax_lub : forall n m p, n <= p -> m <= p -> Zmax n m <= p
 := Z.max_lub.

Definition Zmax_lub_lt : forall n m p:Z, n < p -> m < p -> Zmax n m < p
 := Z.max_lub_lt.


(** * Compatibility with order *)

Definition Zle_max_compat_r : forall n m p, n <= m -> Zmax n p <= Zmax m p
 := Z.max_le_compat_r.

Definition Zle_max_compat_l : forall n m p, n <= m -> Zmax p n <= Zmax p m
 := Z.max_le_compat_l.


(** * Semi-lattice properties of max *)

Definition Zmax_idempotent : forall n, Zmax n n = n := Z.max_id.
Definition Zmax_comm : forall n m, Zmax n m = Zmax m n := Z.max_comm.
Definition Zmax_assoc : forall n m p, Zmax n (Zmax m p) = Zmax (Zmax n m) p
 := Z.max_assoc.

(** * Additional properties of max *)

Lemma Zmax_irreducible_dec : forall n m, {Zmax n m = n} + {Zmax n m = m}.
Proof. exact Z.max_dec. Qed.

Definition Zmax_le_prime : forall n m p, p <= Zmax n m -> p <= n \/ p <= m
 := Z.max_le.


(** * Operations preserving max *)

Definition Zsucc_max_distr :
  forall n m:Z, Zsucc (Zmax n m) = Zmax (Zsucc n) (Zsucc m)
 := Z.succ_max_distr.

Definition Zplus_max_distr_l : forall n m p:Z, Zmax (p + n) (p + m) = p + Zmax n m
 := Z.add_max_distr_l.

Definition Zplus_max_distr_r : forall n m p:Z, Zmax (n + p) (m + p) = Zmax n m + p
 := Z.add_max_distr_r.

(** * Maximum and Zpos *)

Lemma Zpos_max : forall p q, Zpos (Pmax p q) = Zmax (Zpos p) (Zpos q).
Proof.
 intros; unfold Zmax, Pmax; simpl; generalize (Pcompare_Eq_eq p q).
 destruct Pcompare; auto.
 intro H; rewrite H; auto.
Qed.

Lemma Zpos_max_1 : forall p, Zmax 1 (Zpos p) = Zpos p.
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

(* begin hide *)
(* Compatibility *)
Notation Zmax1 := Zle_max_l (only parsing).
Notation Zmax2 := Zle_max_r (only parsing).
Notation Zmax_irreducible_inf := Zmax_irreducible_dec (only parsing).
Notation Zmax_le_prime_inf := Zmax_le_prime (only parsing).
(* end hide *)

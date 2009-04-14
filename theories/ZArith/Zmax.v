(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i $Id$ i*)

Require Import Arith_base.
Require Import BinInt.
Require Import Zcompare.
Require Import Zorder.

Open Local Scope Z_scope.

(******************************************)
(** Maximum of two binary integer numbers *)

Definition Zmax m n :=
  match m ?= n with
    | Eq | Gt => m
    | Lt => n
  end.

(** * Characterization of maximum on binary integer numbers *)

Lemma Zmax_case : forall (n m:Z) (P:Z -> Type), P n -> P m -> P (Zmax n m).
Proof.
  intros n m P H1 H2; unfold Zmax in |- *; case (n ?= m); auto with arith.
Qed.

Lemma Zmax_case_strong : forall (n m:Z) (P:Z -> Type), 
  (m<=n -> P n) -> (n<=m -> P m) -> P (Zmax n m).
Proof.
  intros n m P H1 H2; unfold Zmax, Zle, Zge in *.
  rewrite <- (Zcompare_antisym n m) in H1.
  destruct (n ?= m); (apply H1|| apply H2); discriminate. 
Qed.

Lemma Zmax_spec : forall x y:Z, 
  x >= y /\ Zmax x y = x  \/
  x < y /\ Zmax x y = y.
Proof.
 intros; unfold Zmax, Zlt, Zge.
 destruct (Zcompare x y); [ left | right | left ]; split; auto; discriminate.
Qed.

Lemma Zmax_left : forall n m:Z, n>=m -> Zmax n m = n.
Proof.
  intros n m; unfold Zmax, Zge; destruct (n ?= m); auto.
  intro H; elim H; auto.
Qed.

Lemma Zmax_right : forall n m:Z, n<=m -> Zmax n m = m.
Proof.
  intros n m; unfold Zmax, Zle.
  generalize (Zcompare_Eq_eq n m).
  destruct (n ?= m); auto.
  intros _ H; elim H; auto.
Qed.

(** * Least upper bound properties of max *)

Lemma Zle_max_l : forall n m:Z, n <= Zmax n m.
Proof.
  intros; apply Zmax_case_strong; auto with zarith.
Qed.

Notation Zmax1 := Zle_max_l (only parsing).

Lemma Zle_max_r : forall n m:Z, m <= Zmax n m.
Proof.
  intros; apply Zmax_case_strong; auto with zarith.
Qed.

Notation Zmax2 := Zle_max_r (only parsing).

Lemma Zmax_lub : forall n m p:Z, n <= p -> m <= p -> Zmax n m <= p.
Proof.
  intros; apply Zmax_case; assumption.
Qed.

(** * Semi-lattice properties of max *)

Lemma Zmax_idempotent : forall n:Z, Zmax n n = n.
Proof.
  intros; apply Zmax_case; auto.
Qed.

Lemma Zmax_comm : forall n m:Z, Zmax n m = Zmax m n.
Proof.
  intros; do 2 apply Zmax_case_strong; intros; 
    apply Zle_antisym; auto with zarith.
Qed.

Lemma Zmax_assoc : forall n m p:Z, Zmax n (Zmax m p) = Zmax (Zmax n m) p.
Proof.
  intros n m p; repeat apply Zmax_case_strong; intros; 
    reflexivity || (try apply Zle_antisym); eauto with zarith.
Qed.

(** * Additional properties of max *)

Lemma Zmax_irreducible_dec : forall n m:Z, {Zmax n m = n} + {Zmax n m = m}.
Proof.
  intros; apply Zmax_case; auto.
Qed.

Lemma Zmax_le_prime : forall n m p:Z, p <= Zmax n m -> p <= n \/ p <= m.
Proof.
  intros n m p; apply Zmax_case; auto.
Qed.

(** * Operations preserving max *)

Lemma Zsucc_max_distr : 
  forall n m:Z, Zsucc (Zmax n m) = Zmax (Zsucc n) (Zsucc m).
Proof.
  intros n m; unfold Zmax in |- *; rewrite (Zcompare_succ_compat n m);
    elim_compare n m; intros E; rewrite E; auto with arith.
Qed.

Lemma Zplus_max_distr_l : forall n m p:Z, Zmax (p + n) (p + m) = p + Zmax n m.
Proof.
  intros n m p; unfold Zmax.
  rewrite (Zcompare_plus_compat n m p).
  destruct (n ?= m); trivial.
Qed.

Lemma Zplus_max_distr_r : forall n m p:Z, Zmax (n + p) (m + p) = Zmax n m + p.
Proof.
  intros n m p; repeat rewrite (Zplus_comm _ p); apply Zplus_max_distr_l.
Qed.

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
  intros.
  case_eq (Pcompare p q Eq).
  intros H; rewrite (Pcompare_Eq_eq _ _ H).
  rewrite Zminus_diag.
  unfold Zmax; simpl.
  unfold Pminus; rewrite Pminus_mask_diag; auto.
  intros; rewrite Pminus_Lt; auto.
  destruct (Zmax_spec 1 (Zpos p - Zpos q)) as [(H1,H2)|(H1,H2)]; auto.
  elimtype False; clear H2.
  assert (H1':=Zlt_trans 0 1 _ Zlt_0_1 H1).
  generalize (Zlt_0_minus_lt _ _ H1').
  unfold Zlt; simpl.
  rewrite (ZC2 _ _ H); intro; discriminate.
  intros; simpl; rewrite H.
  symmetry; apply Zpos_max_1.
Qed.

(* begin hide *)
(* Compatibility *)
Notation Zmax_irreducible_inf := Zmax_irreducible_dec (only parsing).
Notation Zmax_le_prime_inf := Zmax_le_prime (only parsing).
(* end hide *)

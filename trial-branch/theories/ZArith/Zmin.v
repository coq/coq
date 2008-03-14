(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i $Id$ i*)

(** Initial version from Pierre Crégut (CNET, Lannion, France), 1996.
    Further extensions by the Coq development team, with suggestions
    from Russell O'Connor (Radbout U., Nijmegen, The Netherlands).
 *)

Require Import Arith_base.
Require Import BinInt.
Require Import Zcompare.
Require Import Old_zorder.

Open Local Scope Z_scope.

(**************************************)
(** Minimum on binary integer numbers *)

Unboxed Definition Zmin (n m:Z) :=
  match n ?= m with
    | Eq | Lt => n
    | Gt => m
  end.

(** * Characterization of the minimum on binary integer numbers *)

Lemma Zmin_case_strong : forall (n m:Z) (P:Z -> Type), 
  (n<=m -> P n) -> (m<=n -> P m) -> P (Zmin n m).
Proof.
  intros n m P H1 H2; unfold Zmin, Zle, Zge in *.
  rewrite <- (Zcompare_antisym n m) in H2.
  destruct (n ?= m); (apply H1|| apply H2); discriminate. 
Qed.

Lemma Zmin_case : forall (n m:Z) (P:Z -> Type), P n -> P m -> P (Zmin n m).
Proof.
  intros n m P H1 H2; unfold Zmin in |- *; case (n ?= m); auto with arith.
Qed.

Lemma Zmin_spec : forall x y:Z, 
  x <= y /\ Zmin x y = x  \/
  x > y /\ Zmin x y = y.
Proof.
 intros; unfold Zmin, Zle, Zgt.
 destruct (Zcompare x y); [ left | left | right ]; split; auto; discriminate.
Qed.

(** * Greatest lower bound properties of min *)

Lemma Zle_min_l : forall n m:Z, Zmin n m <= n.
Proof.
  intros n m; unfold Zmin in |- *; elim_compare n m; intros E; rewrite E;
    [ apply Zle_refl
      | apply Zle_refl
      | apply Zlt_le_weak; apply Zgt_lt; exact E ].
Qed.

Lemma Zle_min_r : forall n m:Z, Zmin n m <= m.
Proof.
  intros n m; unfold Zmin in |- *; elim_compare n m; intros E; rewrite E;
    [ unfold Zle in |- *; rewrite E; discriminate
      | unfold Zle in |- *; rewrite E; discriminate
      | apply Zle_refl ].
Qed.

Lemma Zmin_glb : forall n m p:Z, p <= n -> p <= m -> p <= Zmin n m.
Proof.
  intros; apply Zmin_case; assumption.
Qed.

(** * Semi-lattice properties of min *)

Lemma Zmin_idempotent : forall n:Z, Zmin n n = n.
Proof.
  unfold Zmin in |- *; intros; elim (n ?= n); auto.
Qed.

Notation Zmin_n_n := Zmin_idempotent (only parsing).

Lemma Zmin_comm : forall n m:Z, Zmin n m = Zmin m n.
Proof.
  intros n m; unfold Zmin.
  rewrite <- (Zcompare_antisym n m).
  assert (H:=Zcompare_Eq_eq n m).
  destruct (n ?= m); simpl; auto.
Qed.

Lemma Zmin_assoc : forall n m p:Z, Zmin n (Zmin m p) = Zmin (Zmin n m) p.
Proof.
  intros n m p; repeat apply Zmin_case_strong; intros; 
    reflexivity || (try apply Zle_antisym); eauto with zarith.
Qed.

(** * Additional properties of min *)

Lemma Zmin_irreducible_inf : forall n m:Z, {Zmin n m = n} + {Zmin n m = m}.
Proof.
  unfold Zmin in |- *; intros; elim (n ?= m); auto.
Qed.

Lemma Zmin_irreducible : forall n m:Z, Zmin n m = n \/ Zmin n m = m.
Proof.
  intros n m; destruct (Zmin_irreducible_inf n m); [left|right]; trivial.
Qed.

Notation Zmin_or := Zmin_irreducible (only parsing).

Lemma Zmin_le_prime_inf : forall n m p:Z, Zmin n m <= p -> {n <= p} + {m <= p}.
Proof.
  intros n m p; apply Zmin_case; auto.
Qed.

(** * Operations preserving min *)

Lemma Zsucc_min_distr : 
  forall n m:Z, Zsucc (Zmin n m) = Zmin (Zsucc n) (Zsucc m).
Proof.
  intros n m; unfold Zmin in |- *; rewrite (Zcompare_succ_compat n m);
    elim_compare n m; intros E; rewrite E; auto with arith.
Qed.

Notation Zmin_SS := Zsucc_min_distr (only parsing).

Lemma Zplus_min_distr_r : forall n m p:Z, Zmin (n + p) (m + p) = Zmin n m + p.
Proof.
  intros x y n; unfold Zmin in |- *.
  rewrite (Zplus_comm x n); rewrite (Zplus_comm y n);
    rewrite (Zcompare_plus_compat x y n).
  case (x ?= y); apply Zplus_comm.
Qed.

Notation Zmin_plus := Zplus_min_distr_r (only parsing).

(** * Minimum and Zpos *)

Lemma Zpos_min : forall p q, Zpos (Pmin p q) = Zmin (Zpos p) (Zpos q).
Proof.
  intros; unfold Zmin, Pmin; simpl; destruct Pcompare; auto.
Qed.


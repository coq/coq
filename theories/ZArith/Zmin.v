(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i $Id$ i*)

(** Binary Integers (Pierre Crégut (CNET, Lannion, France) *)

Require Import Arith.
Require Import BinInt.
Require Import Zcompare.
Require Import Zorder.

Open Local Scope Z_scope.

(**********************************************************************)
(** Minimum on binary integer numbers *)

Definition Zmin (n m:Z) :=
  match n ?= m return Z with
  | Eq => n
  | Lt => n
  | Gt => m
  end.

(** Properties of minimum on binary integer numbers *)

Lemma Zmin_SS : forall n m:Z, Zsucc (Zmin n m) = Zmin (Zsucc n) (Zsucc m).
Proof.
intros n m; unfold Zmin in |- *; rewrite (Zcompare_succ_compat n m);
 elim_compare n m; intros E; rewrite E; auto with arith.
Qed.

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

Lemma Zmin_case : forall (n m:Z) (P:Z -> Set), P n -> P m -> P (Zmin n m).
Proof.
intros n m P H1 H2; unfold Zmin in |- *; case (n ?= m); auto with arith.
Qed.

Lemma Zmin_or : forall n m:Z, Zmin n m = n \/ Zmin n m = m.
Proof.
unfold Zmin in |- *; intros; elim (n ?= m); auto.
Qed.

Lemma Zmin_n_n : forall n:Z, Zmin n n = n.
Proof.
unfold Zmin in |- *; intros; elim (n ?= n); auto.
Qed.

Lemma Zmin_plus : forall n m p:Z, Zmin (n + p) (m + p) = Zmin n m + p.
Proof.
intros x y n; unfold Zmin in |- *.
rewrite (Zplus_comm x n); rewrite (Zplus_comm y n);
 rewrite (Zcompare_plus_compat x y n).
case (x ?= y); apply Zplus_comm.
Qed.

(**********************************************************************)
(** Maximum of two binary integer numbers *)

Definition Zmax a b := match a ?= b with
                       | Lt => b
                       | _ => a
                       end.

(** Properties of maximum on binary integer numbers *)

Ltac CaseEq name :=
  generalize (refl_equal name); pattern name at -1 in |- *; case name.

Theorem Zmax1 : forall a b, a <= Zmax a b.
Proof.
intros a b; unfold Zmax in |- *; CaseEq (a ?= b); simpl in |- *;
 auto with zarith.
unfold Zle in |- *; intros H; rewrite H; red in |- *; intros; discriminate.
Qed.

Theorem Zmax2 : forall a b, b <= Zmax a b.
Proof.
intros a b; unfold Zmax in |- *; CaseEq (a ?= b); simpl in |- *;
 auto with zarith.
intros H;
 (case (Zle_or_lt b a); auto; unfold Zlt in |- *; rewrite H; intros;
   discriminate).
intros H;
 (case (Zle_or_lt b a); auto; unfold Zlt in |- *; rewrite H; intros;
   discriminate).
Qed.

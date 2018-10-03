(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Binary Integers : results about Z.compare *)
(** Initial author: Pierre Crégut (CNET, Lannion, France *)

(** THIS FILE IS DEPRECATED.
    It is now almost entirely made of compatibility formulations
    for results already present in BinInt.Z. *)

Require Export BinPos BinInt.
Require Import Lt Gt Plus Mult. (* Useless now, for compatibility only *)

Local Open Scope Z_scope.

(***************************)
(** * Comparison on integers *)

Lemma Zcompare_Gt_Lt_antisym : forall n m:Z, (n ?= m) = Gt <-> (m ?= n) = Lt.
Proof Z.gt_lt_iff.

Lemma Zcompare_antisym n m : CompOpp (n ?= m) = (m ?= n).
Proof eq_sym (Z.compare_antisym n m).

(** * Transitivity of comparison *)

Lemma Zcompare_Lt_trans :
  forall n m p:Z, (n ?= m) = Lt -> (m ?= p) = Lt -> (n ?= p) = Lt.
Proof Z.lt_trans.

Lemma Zcompare_Gt_trans :
  forall n m p:Z, (n ?= m) = Gt -> (m ?= p) = Gt -> (n ?= p) = Gt.
Proof.
 intros n m p. change (n > m -> m > p -> n > p).
 Z.swap_greater. intros. now transitivity m.
Qed.

(** * Comparison and opposite *)

Lemma Zcompare_opp n m : (n ?= m) = (- m ?= - n).
Proof.
 symmetry. apply Z.compare_opp.
Qed.

(** * Comparison first-order specification *)

Lemma Zcompare_Gt_spec n m : (n ?= m) = Gt ->  exists h, n + - m = Zpos h.
Proof.
 rewrite Z.compare_sub. unfold Z.sub.
 destruct (n+-m) as [|p|p]; try discriminate. now exists p.
Qed.

(** * Comparison and addition *)

Lemma Zcompare_plus_compat n m p : (p + n ?= p + m) = (n ?= m).
Proof.
 apply Z.add_compare_mono_l.
Qed.

Lemma Zplus_compare_compat (r:comparison) (n m p q:Z) :
  (n ?= m) = r -> (p ?= q) = r -> (n + p ?= m + q) = r.
Proof.
 rewrite (Z.compare_sub n), (Z.compare_sub p), (Z.compare_sub (n+p)).
 unfold Z.sub. rewrite Z.opp_add_distr. rewrite Z.add_shuffle1.
 destruct (n+-m), (p+-q); simpl; intros; now subst.
Qed.

Lemma Zcompare_succ_Gt n : (Z.succ n ?= n) = Gt.
Proof.
 apply Z.lt_gt. apply Z.lt_succ_diag_r.
Qed.

Lemma Zcompare_Gt_not_Lt n m : (n ?= m) = Gt <-> (n ?= m+1) <> Lt.
Proof.
 change (n > m <-> n >= m+1). Z.swap_greater. symmetry. apply Z.le_succ_l.
Qed.

(** * Successor and comparison *)

Lemma Zcompare_succ_compat n m : (Z.succ n ?= Z.succ m) = (n ?= m).
Proof.
 rewrite <- 2 Z.add_1_l. apply Z.add_compare_mono_l.
Qed.

(** * Multiplication and comparison *)

Lemma Zcompare_mult_compat :
  forall (p:positive) (n m:Z), (Zpos p * n ?= Zpos p * m) = (n ?= m).
Proof.
 intros p [|n|n] [|m|m]; simpl; trivial; now rewrite Pos.mul_compare_mono_l.
Qed.

Lemma Zmult_compare_compat_l n m p:
  p > 0 -> (n ?= m) = (p * n ?= p * m).
Proof.
 intros; destruct p; try discriminate.
 symmetry. apply Zcompare_mult_compat.
Qed.

Lemma Zmult_compare_compat_r n m p :
  p > 0 -> (n ?= m) = (n * p ?= m * p).
Proof.
 intros; rewrite 2 (Z.mul_comm _ p); now apply Zmult_compare_compat_l.
Qed.

(** * Relating [x ?= y] to [=], [<=], [<], [>=] or [>] *)

Lemma Zcompare_elim :
  forall (c1 c2 c3:Prop) (n m:Z),
    (n = m -> c1) ->
    (n < m -> c2) ->
    (n > m -> c3) -> match n ?= m with
                       | Eq => c1
                       | Lt => c2
                       | Gt => c3
                     end.
Proof.
 intros. case Z.compare_spec; trivial. now Z.swap_greater.
Qed.

Lemma Zcompare_eq_case :
  forall (c1 c2 c3:Prop) (n m:Z),
    c1 -> n = m -> match n ?= m with
                     | Eq => c1
                     | Lt => c2
                     | Gt => c3
                   end.
Proof.
 intros. subst. now rewrite Z.compare_refl.
Qed.

Lemma Zle_compare :
  forall n m:Z,
    n <= m -> match n ?= m with
		| Eq => True
		| Lt => True
		| Gt => False
              end.
Proof.
  intros. case Z.compare_spec; trivial; Z.order.
Qed.

Lemma Zlt_compare :
  forall n m:Z,
   n < m -> match n ?= m with
              | Eq => False
              | Lt => True
              | Gt => False
            end.
Proof.
  intros x y H; now rewrite H.
Qed.

Lemma Zge_compare :
  forall n m:Z,
    n >= m -> match n ?= m with
		| Eq => True
		| Lt => False
		| Gt => True
              end.
Proof.
  intros. now case Z.compare_spec.
Qed.

Lemma Zgt_compare :
  forall n m:Z,
    n > m -> match n ?= m with
               | Eq => False
               | Lt => False
               | Gt => True
             end.
Proof.
  intros x y H; now rewrite H.
Qed.

(** Compatibility notations *)

Notation Zcompare_refl := Z.compare_refl (compat "8.7").
Notation Zcompare_Eq_eq := Z.compare_eq (only parsing).
Notation Zcompare_Eq_iff_eq := Z.compare_eq_iff (only parsing).
Notation Zcompare_spec := Z.compare_spec (compat "8.7").
Notation Zmin_l := Z.min_l (compat "8.7").
Notation Zmin_r := Z.min_r (compat "8.7").
Notation Zmax_l := Z.max_l (compat "8.7").
Notation Zmax_r := Z.max_r (compat "8.7").
Notation Zabs_eq := Z.abs_eq (compat "8.7").
Notation Zabs_non_eq := Z.abs_neq (only parsing).
Notation Zsgn_0 := Z.sgn_null (only parsing).
Notation Zsgn_1 := Z.sgn_pos (only parsing).
Notation Zsgn_m1 := Z.sgn_neg (only parsing).

(** Not kept: Zcompare_egal_dec *)

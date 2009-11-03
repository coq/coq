(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

Require Import DecidableType2 Morphisms RelationPairs.
Set Implicit Arguments.
Unset Strict Implicit.

(** * Examples of Decidable Type structures. *)


(** From two decidable types, we can build a new DecidableType
   over their cartesian product. *)

Module PairDecidableType(D1 D2:DecidableType) <: DecidableType.

 Definition t := (D1.t * D2.t)%type.

 Definition eq := (D1.eq * D2.eq)%signature.

 Instance eq_equiv : Equivalence eq.

 Definition eq_dec : forall x y, { eq x y }+{ ~eq x y }.
 Proof.
 intros (x1,x2) (y1,y2); unfold eq; simpl.
 destruct (D1.eq_dec x1 y1); destruct (D2.eq_dec x2 y2);
  compute; intuition.
 Defined.

End PairDecidableType.

(** Similarly for pairs of UsualDecidableType *)

Module PairUsualDecidableType(D1 D2:UsualDecidableType) <: UsualDecidableType.
 Definition t := (D1.t * D2.t)%type.
 Definition eq := @eq t.
 Program Instance eq_equiv : Equivalence eq.
 Definition eq_dec : forall x y, { eq x y }+{ ~eq x y }.
 Proof.
 intros (x1,x2) (y1,y2);
 destruct (D1.eq_dec x1 y1); destruct (D2.eq_dec x2 y2);
 unfold eq, D1.eq, D2.eq in *; simpl;
 (left; f_equal; auto; fail) ||
 (right; intro H; injection H; auto).
 Defined.

End PairUsualDecidableType.

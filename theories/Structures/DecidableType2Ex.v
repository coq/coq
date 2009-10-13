(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

Require Import DecidableType2.
Set Implicit Arguments.
Unset Strict Implicit.

(** * Examples of Decidable Type structures. *)

(** A particular case of [DecidableType] where
    the equality is the usual one of Coq. *)

Module Type UsualDecidableType.
 Parameter Inline t : Type.
 Definition eq := @eq t.
 Program Instance eq_equiv : Equivalence eq.
 Parameter eq_dec : forall x y, { eq x y }+{~eq x y }.
End UsualDecidableType.

(** a [UsualDecidableType] is in particular an [DecidableType]. *)

Module UDT_to_DT (U:UsualDecidableType) <: DecidableType := U.

(** an shortcut for easily building a UsualDecidableType *)

Module Type MiniDecidableType.
 Parameter Inline t : Type.
 Parameter eq_dec : forall x y:t, { x=y }+{ x<>y }.
End MiniDecidableType.

Module Make_UDT (M:MiniDecidableType) <: UsualDecidableType.
 Definition t:=M.t.
 Definition eq := @eq t.
 Program Instance eq_equiv : Equivalence eq.
 Definition eq_dec := M.eq_dec.
End Make_UDT.

(** From two decidable types, we can build a new DecidableType
   over their cartesian product. *)

Module PairDecidableType(D1 D2:DecidableType) <: DecidableType.

 Definition t := prod D1.t D2.t.

 Definition eq x y := D1.eq (fst x) (fst y) /\ D2.eq (snd x) (snd y).

 Instance eq_equiv : Equivalence eq.
 Proof.
 constructor.
 intros (x1,x2); red; simpl; auto.
 intros (x1,x2) (y1,y2); unfold eq; simpl; intuition.
 intros (x1,x2) (y1,y2) (z1,z2); unfold eq; simpl; intuition eauto.
 Qed.

 Definition eq_dec : forall x y, { eq x y }+{ ~eq x y }.
 Proof.
 intros (x1,x2) (y1,y2); unfold eq; simpl.
 destruct (D1.eq_dec x1 y1); destruct (D2.eq_dec x2 y2); intuition.
 Defined.

End PairDecidableType.

(** Similarly for pairs of UsualDecidableType *)

Module PairUsualDecidableType(D1 D2:UsualDecidableType) <: UsualDecidableType.
 Definition t := prod D1.t D2.t.
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

(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

Require Import DecidableType OrderedType OrderedTypeEx.
Set Implicit Arguments.
Unset Strict Implicit.

(** * Examples of Decidable Type structures. *)

(** A particular case of [DecidableType] where 
    the equality is the usual one of Coq. *)

Module Type UsualDecidableType.
 Parameter Inline t : Set.
 Definition eq := @eq t.
 Definition eq_refl := @refl_equal t.
 Definition eq_sym := @sym_eq t.
 Definition eq_trans := @trans_eq t.
 Parameter eq_dec : forall x y, { eq x y }+{~eq x y }.
End UsualDecidableType.

(** a [UsualDecidableType] is in particular an [DecidableType]. *)

Module UDT_to_DT (U:UsualDecidableType) <: DecidableType := U.

(** an shortcut for easily building a UsualDecidableType *)

Module Type MiniDecidableType. 
 Parameter Inline t : Set.
 Parameter eq_dec : forall x y:t, { x=y }+{ x<>y }.
End MiniDecidableType. 

Module Make_UDT (M:MiniDecidableType) <: UsualDecidableType.
 Definition t:=M.t. 
 Definition eq := @eq t.
 Definition eq_refl := @refl_equal t.
 Definition eq_sym := @sym_eq t.
 Definition eq_trans := @trans_eq t.
 Definition eq_dec := M.eq_dec.
End Make_UDT.

(** An OrderedType can be seen as a DecidableType *)

Module OT_as_DT (O:OrderedType) <: DecidableType. 
 Module OF := OrderedTypeFacts O.
 Definition t := O.t.
 Definition eq := O.eq. 
 Definition eq_refl := O.eq_refl. 
 Definition eq_sym := O.eq_sym. 
 Definition eq_trans := O.eq_trans. 
 Definition eq_dec := OF.eq_dec. 
End OT_as_DT.

(** (Usual) Decidable Type for [nat], [positive], [N], [Z] *)

Module Nat_as_DT <: UsualDecidableType := OT_as_DT (Nat_as_OT).
Module Positive_as_DT <: UsualDecidableType := OT_as_DT (Positive_as_OT).
Module N_as_DT <: UsualDecidableType := OT_as_DT (N_as_OT).
Module Z_as_DT <: UsualDecidableType := OT_as_DT (Z_as_OT).

(** From two decidable types, we can build a new DecidableType 
   over their cartesian product. *)

Module PairDecidableType(D1 D2:DecidableType) <: DecidableType.

 Definition t := prod D1.t D2.t.

 Definition eq x y := D1.eq (fst x) (fst y) /\ D2.eq (snd x) (snd y).

 Lemma eq_refl : forall x : t, eq x x.
 Proof. 
 intros (x1,x2); red; simpl; auto.
 Qed.

 Lemma eq_sym : forall x y : t, eq x y -> eq y x.
 Proof. 
 intros (x1,x2) (y1,y2); unfold eq; simpl; intuition.
 Qed.

 Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
 Proof. 
 intros (x1,x2) (y1,y2) (z1,z2); unfold eq; simpl; intuition eauto.
 Qed.

 Definition eq_dec : forall x y, { eq x y }+{ ~eq x y }.
 Proof.
 intros (x1,x2) (y1,y2); unfold eq; simpl.
 destruct (D1.eq_dec x1 y1); destruct (D2.eq_dec x2 y2); intuition.
 Defined.

End PairDecidableType.

(** Similarly for pairs of UsualDecidableType *)

Module PairUsualDecidableType(D1 D2:UsualDecidableType) <: DecidableType.
 Definition t := prod D1.t D2.t.
 Definition eq := @eq t.
 Definition eq_refl := @refl_equal t.
 Definition eq_sym := @sym_eq t.
 Definition eq_trans := @trans_eq t.
 Definition eq_dec : forall x y, { eq x y }+{ ~eq x y }.
 Proof.
 intros (x1,x2) (y1,y2); 
 destruct (D1.eq_dec x1 y1); destruct (D2.eq_dec x2 y2); 
 unfold eq, D1.eq, D2.eq in *; simpl; 
 (left; f_equal; auto; fail) || 
 (right; intro H; injection H; auto).
 Defined.

End PairUsualDecidableType.

(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import DecidableType OrderedType OrderedTypeEx.
Set Implicit Arguments.
Unset Strict Implicit.

(** NB: This file is here only for compatibility with earlier version of
    [FSets] and [FMap]. Please use [Structures/Equalities.v] directly now. *)

(** * Examples of Decidable Type structures. *)

(** A particular case of [DecidableType] where
    the equality is the usual one of Coq. *)

Module Type UsualDecidableType := Equalities.UsualDecidableTypeOrig.

(** a [UsualDecidableType] is in particular an [DecidableType]. *)

Module UDT_to_DT (U:UsualDecidableType) <: DecidableType := U.

(** an shortcut for easily building a UsualDecidableType *)

Module Type MiniDecidableType := Equalities.MiniDecidableType.

Module Make_UDT (M:MiniDecidableType) <: UsualDecidableType
 := Equalities.Make_UDT M.

(** An OrderedType can now directly be seen as a DecidableType *)

Module OT_as_DT (O:OrderedType) <: DecidableType := O.

(** (Usual) Decidable Type for [nat], [positive], [N], [Z] *)

Module Nat_as_DT <: UsualDecidableType := Nat_as_OT.
Module Positive_as_DT <: UsualDecidableType := Positive_as_OT.
Module N_as_DT <: UsualDecidableType := N_as_OT.
Module Z_as_DT <: UsualDecidableType := Z_as_OT.

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

Module PairUsualDecidableType(D1 D2:UsualDecidableType) <: UsualDecidableType.
 Definition t := prod D1.t D2.t.
 Definition eq := @eq t.
 Definition eq_refl := @eq_refl t.
 Definition eq_sym := @eq_sym t.
 Definition eq_trans := @eq_trans t.
 Definition eq_dec : forall x y, { eq x y }+{ ~eq x y }.
 Proof.
 intros (x1,x2) (y1,y2);
 destruct (D1.eq_dec x1 y1); destruct (D2.eq_dec x2 y2);
 unfold eq, D1.eq, D2.eq in *; simpl;
 (left; f_equal; auto; fail) ||
 (right; injection; auto).
 Defined.

End PairUsualDecidableType.

(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Finite sets library.
 * Authors: Pierre Letouzey and Jean-Christophe Filliâtre
 * Institution: LRI, CNRS UMR 8623 - Université Paris Sud
 *              91405 Orsay, France *)

Require Import Orders PeanoNat POrderedType BinNat BinInt
 RelationPairs EqualitiesFacts.

(** * Examples of Ordered Type structures. *)


(** Ordered Type for [nat], [Positive], [N], [Z] with the usual order. *)

Module Nat_as_OT := PeanoNat.Nat.
Module Positive_as_OT := BinPos.Pos.
Module N_as_OT := BinNat.N.
Module Z_as_OT := BinInt.Z.

(** An OrderedType can now directly be seen as a DecidableType *)

Module OT_as_DT (O:OrderedType) <: DecidableType := O.

(** (Usual) Decidable Type for [nat], [positive], [N], [Z] *)

Module Nat_as_DT <: UsualDecidableType := Nat_as_OT.
Module Positive_as_DT <: UsualDecidableType := Positive_as_OT.
Module N_as_DT <: UsualDecidableType := N_as_OT.
Module Z_as_DT <: UsualDecidableType := Z_as_OT.



(** From two ordered types, we can build a new OrderedType
   over their cartesian product, using the lexicographic order. *)

Module PairOrderedType(O1 O2:OrderedType) <: OrderedType.
 Include PairDecidableType O1 O2.

 Definition lt :=
   (relation_disjunction (O1.lt @@1) (O1.eq * O2.lt))%signature.

 Instance lt_strorder : StrictOrder lt.
 Proof.
 split.
 (* irreflexive *)
 intros (x1,x2); compute. destruct 1.
 apply (StrictOrder_Irreflexive x1); auto.
 apply (StrictOrder_Irreflexive x2); intuition.
 (* transitive *)
 intros (x1,x2) (y1,y2) (z1,z2). compute. intuition.
 left; etransitivity; eauto.
 left. setoid_replace z1 with y1; auto with relations.
 left; setoid_replace x1 with y1; auto with relations.
 right; split; etransitivity; eauto.
 Qed.

 Instance lt_compat : Proper (eq==>eq==>iff) lt.
 Proof.
 compute.
 intros (x1,x2) (x1',x2') (X1,X2) (y1,y2) (y1',y2') (Y1,Y2).
 rewrite X1,X2,Y1,Y2; intuition.
 Qed.

 Definition compare x y :=
  match O1.compare (fst x) (fst y) with
   | Eq => O2.compare (snd x) (snd y)
   | Lt => Lt
   | Gt => Gt
  end.

 Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
 Proof.
 intros (x1,x2) (y1,y2); unfold compare; simpl.
 destruct (O1.compare_spec x1 y1); try (constructor; compute; auto).
 destruct (O2.compare_spec x2 y2); constructor; compute; auto with relations.
 Qed.

End PairOrderedType.

(** Even if [positive] can be seen as an ordered type with respect to the
  usual order (see above), we can also use a lexicographic order over bits
  (lower bits are considered first). This is more natural when using
  [positive] as indexes for sets or maps (see MSetPositive). *)

Local Open Scope positive.

Module PositiveOrderedTypeBits <: UsualOrderedType.
  Definition t:=positive.
  Include HasUsualEq <+ UsualIsEq.
  Definition eqb := Pos.eqb.
  Definition eqb_eq := Pos.eqb_eq.
  Include HasEqBool2Dec.

  Fixpoint bits_lt (p q:positive) : Prop :=
   match p, q with
   | xH, xI _ => True
   | xH, _ => False
   | xO p, xO q => bits_lt p q
   | xO _, _ => True
   | xI p, xI q => bits_lt p q
   | xI _, _ => False
   end.

  Definition lt:=bits_lt.

  Lemma bits_lt_antirefl : forall x : positive, ~ bits_lt x x.
  Proof.
   induction x; simpl; auto.
  Qed.

  Lemma bits_lt_trans :
    forall x y z : positive, bits_lt x y -> bits_lt y z -> bits_lt x z.
  Proof.
   induction x; destruct y,z; simpl; eauto; intuition.
  Qed.

  Instance lt_compat : Proper (eq==>eq==>iff) lt.
  Proof.
   intros x x' Hx y y' Hy. rewrite Hx, Hy; intuition.
  Qed.

  Instance lt_strorder : StrictOrder lt.
  Proof.
   split; [ exact bits_lt_antirefl | exact bits_lt_trans ].
  Qed.

  Fixpoint compare x y :=
    match x, y with
      | x~1, y~1 => compare x y
      | x~1, _ => Gt
      | x~0, y~0 => compare x y
      | x~0, _ => Lt
      | 1, y~1 => Lt
      | 1, 1 => Eq
      | 1, y~0 => Gt
    end.

  Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
  Proof.
   unfold eq, lt.
   induction x; destruct y; try constructor; simpl; auto.
    destruct (IHx y); subst; auto.
    destruct (IHx y); subst; auto.
  Qed.

End PositiveOrderedTypeBits.

(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Finite sets library.
 * Authors: Pierre Letouzey and Jean-Christophe Filliâtre
 * Institution: LRI, CNRS UMR 8623 - Université Paris Sud
 *              91405 Orsay, France *)

(* $Id$ *)

Require Import OrderedType2 NatOrderedType POrderedType NOrderedType
 ZOrderedType DecidableType2Ex RelationPairs.

(** * Examples of Ordered Type structures. *)


(** Ordered Type for [nat], [Positive], [N], [Z] with the usual order. *)

Module Nat_as_OT := NatOrderedType.Nat_as_OT.
Module Positive_as_OT := POrderedType.Positive_as_OT.
Module N_as_OT := NOrderedType.N_as_OT.
Module Z_as_OT := ZOrderedType.Z_as_OT.

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
   (relation_disjunction (O1.lt @@ fst) (O1.eq * O2.lt))%signature.

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
 left; rewrite <- H0; auto.
 left; rewrite H; auto.
 right; split; eauto. etransitivity; eauto.
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

 Lemma compare_spec : forall x y, Cmp eq lt x y (compare x y).
 Proof.
 intros (x1,x2) (y1,y2); unfold compare; simpl.
 destruct (O1.compare_spec x1 y1); try (constructor; compute; auto).
 destruct (O2.compare_spec x2 y2); constructor; compute; auto.
 Qed.

End PairOrderedType.


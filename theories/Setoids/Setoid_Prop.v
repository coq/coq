
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$: i*)

Require Import Setoid_tac.

(** * A few examples on [iff] *)

(** [iff] as a relation *)

Add Relation Prop iff
  reflexivity proved by iff_refl
  symmetry proved by iff_sym
  transitivity proved by iff_trans
as iff_relation.

(** [impl] as a relation *)

Theorem impl_trans: transitive _ impl.
Proof.
  hnf; unfold impl; tauto.
Qed.

Add Relation Prop impl
  reflexivity proved by impl_refl
  transitivity proved by impl_trans
as impl_relation.

(** [impl] is a morphism *)

Add Morphism impl with signature iff ==> iff ==> iff as Impl_Morphism.
Proof.
  unfold impl; tauto.
Qed.

(** [and] is a morphism *)

Add Morphism and with signature iff ==> iff ==> iff as And_Morphism.
 tauto.
Qed.

(** [or] is a morphism *)

Add Morphism or with signature iff ==> iff ==> iff as Or_Morphism.
Proof.
  tauto.
Qed.

(** [not] is a morphism *)

Add Morphism not with signature iff ==> iff as Not_Morphism.
Proof.
  tauto.
Qed.

(** The same examples on [impl] *)

Add Morphism and with signature impl ++> impl ++> impl as And_Morphism2.
Proof.
  unfold impl; tauto.
Qed.

Add Morphism or with signature impl ++> impl ++> impl as Or_Morphism2.
Proof.
  unfold impl; tauto.
Qed.

Add Morphism not with signature impl --> impl as Not_Morphism2.
Proof.
  unfold impl; tauto.
Qed.


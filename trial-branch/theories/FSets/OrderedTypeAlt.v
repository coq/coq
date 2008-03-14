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

Require Import OrderedType.

(** * An alternative (but equivalent) presentation for an Ordered Type inferface. *)

(** NB: [comparison], defined in [theories/Init/datatypes.v] is [Eq|Lt|Gt]
whereas [compare], defined in [theories/FSets/OrderedType.v] is [EQ _ | LT _ | GT _ ] 
*)

Module Type OrderedTypeAlt.

 Parameter t : Set.
 
 Parameter compare : t -> t -> comparison.

 Infix "?=" := compare (at level 70, no associativity).

 Parameter compare_sym : 
   forall x y, (y?=x) = CompOpp (x?=y).
 Parameter compare_trans : 
   forall c x y z, (x?=y) = c -> (y?=z) = c -> (x?=z) = c.

End OrderedTypeAlt. 

(** From this new presentation to the original one. *)

Module OrderedType_from_Alt (O:OrderedTypeAlt) <: OrderedType.
 Import O.

 Definition t := t.

 Definition eq x y := (x?=y) = Eq.
 Definition lt x y := (x?=y) = Lt.

 Lemma eq_refl : forall x, eq x x.
 Proof.
 intro x.
 unfold eq.
 assert (H:=compare_sym x x).
 destruct (x ?= x); simpl in *; try discriminate; auto.
 Qed.

 Lemma eq_sym : forall x y, eq x y -> eq y x.
 Proof. 
 unfold eq; intros.
 rewrite compare_sym.
 rewrite H; simpl; auto.
 Qed.

 Definition eq_trans := (compare_trans Eq).

 Definition lt_trans := (compare_trans Lt).

 Lemma lt_not_eq : forall x y, lt x y -> ~eq x y.
 Proof.
 unfold eq, lt; intros.
 rewrite H; discriminate.
 Qed.

 Definition compare : forall x y, Compare lt eq x y.
 Proof.
 intros.
 case_eq (x ?= y); intros.
 apply EQ; auto.
 apply LT; auto.
 apply GT; red.
 rewrite compare_sym; rewrite H; auto.
 Defined.

End OrderedType_from_Alt. 

(** From the original presentation to this alternative one. *)

Module OrderedType_to_Alt (O:OrderedType) <: OrderedTypeAlt.
 Import O.
 Module MO:=OrderedTypeFacts(O).
 Import MO.

 Definition t := t.

 Definition compare x y := match compare x y with 
   | LT _ => Lt
   | EQ _ => Eq
   | GT _ => Gt
  end. 

 Infix "?=" := compare (at level 70, no associativity).

 Lemma compare_sym : 
   forall x y, (y?=x) = CompOpp (x?=y).
 Proof.
 intros x y.
 unfold compare.
 destruct (O.compare y x); elim_comp; simpl; auto.
 Qed.
 
 Lemma compare_trans : 
   forall c x y z, (x?=y) = c -> (y?=z) = c -> (x?=z) = c.
 Proof.
 intros c x y z.
 destruct c; unfold compare.
 destruct (O.compare x y); intros; try discriminate.
 destruct (O.compare y z); intros; try discriminate.
 elim_comp; auto.
 destruct (O.compare x y); intros; try discriminate.
 destruct (O.compare y z); intros; try discriminate.
 elim_comp; auto.
 destruct (O.compare x y); intros; try discriminate.
 destruct (O.compare y z); intros; try discriminate.
 elim_comp; auto.
 Qed.

End OrderedType_to_Alt.

 

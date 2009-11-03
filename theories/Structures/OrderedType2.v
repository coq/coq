(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

Require Export Relations Morphisms Setoid DecidableType2.
Set Implicit Arguments.
Unset Strict Implicit.

(** * Ordered types *)

Inductive Cmp {A} (eq lt:relation A)(x y : A) : comparison -> Prop :=
| Cmp_eq : eq x y -> Cmp eq lt x y Eq
| Cmp_lt : lt x y -> Cmp eq lt x y Lt
| Cmp_gt : lt y x -> Cmp eq lt x y Gt.

Hint Constructors Cmp.


Module Type MiniOrderedType.
  Include Type EqualityType.

  Parameter Inline lt : t -> t -> Prop.
  Instance lt_strorder : StrictOrder lt.
  Instance lt_compat : Proper (eq==>eq==>iff) lt.

  Parameter compare : t -> t -> comparison.
  Axiom compare_spec : forall x y, Cmp eq lt x y (compare x y).

End MiniOrderedType.


Module Type OrderedType.
  Include Type MiniOrderedType.

  (** A [eq_dec] can be deduced from [compare] below. But adding this
     redundant field allows to see an OrderedType as a DecidableType. *)
  Parameter eq_dec : forall x y, { eq x y } + { ~ eq x y }.

End OrderedType.


Module MOT_to_OT (Import O : MiniOrderedType) <: OrderedType.
  Include O.

  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
   intros.
   assert (H:=compare_spec x y); destruct (compare x y).
   left; inversion_clear H; auto.
   right; inversion_clear H. intro H'. rewrite H' in *.
      apply (StrictOrder_Irreflexive y); auto.
   right; inversion_clear H. intro H'. rewrite H' in *.
      apply (StrictOrder_Irreflexive y); auto.
  Defined.

End MOT_to_OT.


(** * UsualOrderedType

    A particular case of [OrderedType] where the equality is
    the usual one of Coq. *)

Module Type UsualOrderedType.
 Include Type UsualDecidableType.

 Parameter Inline lt : t -> t -> Prop.
 Instance lt_strorder : StrictOrder lt.
 (* The following is useless since eq is Leibniz, but should be there
    for subtyping... *)
 Instance lt_compat : Proper (eq==>eq==>iff) lt.

 Parameter compare : t -> t -> comparison.
 Axiom compare_spec : forall x y, Cmp eq lt x y (compare x y).

End UsualOrderedType.

(** a [UsualOrderedType] is in particular an [OrderedType]. *)

Module UOT_to_OT (U:UsualOrderedType) <: OrderedType := U.


(** * OrderedType with also a [<=] predicate *)

Module Type OrderedTypeFull.
 Include Type OrderedType.
 Parameter Inline le : t -> t -> Prop.
 Axiom le_lteq : forall x y, le x y <-> lt x y \/ eq x y.
End OrderedTypeFull.

Module OT_to_Full (O:OrderedType) <: OrderedTypeFull.
 Include O.
 Definition le x y := lt x y \/ eq x y.
 Lemma le_lteq : forall x y, le x y <-> lt x y \/ eq x y.
 Proof. unfold le; split; auto. Qed.
End OT_to_Full.


(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

Require Export Relations Morphisms Setoid Equalities.
Set Implicit Arguments.
Unset Strict Implicit.

(** * Ordered types *)

(** First, signatures with only the order relations *)

Module Type HasLt (Import T:Typ).
  Parameter Inline lt : t -> t -> Prop.
End HasLt.

Module Type HasLe (Import T:Typ).
  Parameter Inline le : t -> t -> Prop.
End HasLe.

Module Type EqLt := Typ <+ HasEq <+ HasLt.
Module Type EqLe := Typ <+ HasEq <+ HasLe.
Module Type EqLtLe := Typ <+ HasEq <+ HasLt <+ HasLe.

(** Versions with nice notations *)

Module Type LtNotation (E:EqLt).
  Infix "<" := E.lt.
  Notation "x > y" := (y<x) (only parsing).
  Notation "x < y < z" := (x<y /\ y<z).
End LtNotation.

Module Type LeNotation (E:EqLe).
  Infix "<=" := E.le.
  Notation "x >= y" := (y<=x) (only parsing).
  Notation "x <= y <= z" := (x<=y /\ y<=z).
End LeNotation.

Module Type LtLeNotation (E:EqLtLe).
  Include LtNotation E <+ LeNotation E.
  Notation "x <= y < z" := (x<=y /\ y<z).
  Notation "x < y <= z" := (x<y /\ y<=z).
End LtLeNotation.

Module Type EqLtNotation (E:EqLt) := EqNotation E <+ LtNotation E.
Module Type EqLeNotation (E:EqLe) := EqNotation E <+ LeNotation E.
Module Type EqLtLeNotation (E:EqLtLe) := EqNotation E <+ LtLeNotation E.

Module Type EqLt' := EqLt <+ EqLtNotation.
Module Type EqLe' := EqLe <+ EqLeNotation.
Module Type EqLtLe' := EqLtLe <+ EqLtLeNotation.

(** Versions with logical specifications *)

Module Type IsStrOrder (Import E:EqLt).
  Declare Instance lt_strorder : StrictOrder lt.
  Declare Instance lt_compat : Proper (eq==>eq==>iff) lt.
End IsStrOrder.

Module Type LeIsLtEq (Import E:EqLtLe').
  Axiom le_lteq : forall x y, x<=y <-> x<y \/ x==y.
End LeIsLtEq.

Module Type HasCompare (Import E:EqLt).
  Parameter Inline compare : t -> t -> comparison.
  Axiom compare_spec : forall x y, CompSpec eq lt x y (compare x y).
End HasCompare.

Module Type StrOrder := EqualityType <+ HasLt <+ IsStrOrder.
Module Type DecStrOrder := StrOrder <+ HasCompare.
Module Type OrderedType <: DecidableType := DecStrOrder <+ HasEqDec.
Module Type OrderedTypeFull := OrderedType <+ HasLe <+ LeIsLtEq.

Module Type StrOrder' := StrOrder <+ EqLtNotation.
Module Type DecStrOrder' := DecStrOrder <+ EqLtNotation.
Module Type OrderedType' := OrderedType <+ EqLtNotation.
Module Type OrderedTypeFull' := OrderedTypeFull <+ EqLtLeNotation.


(** NB: in [OrderedType], an [eq_dec] could be deduced from [compare].
  But adding this redundant field allows to see an [OrderedType] as a
  [DecidableType]. *)

(** * Versions with [eq] being the usual Leibniz equality of Coq *)

Module Type UsualStrOrder := UsualEqualityType <+ HasLt <+ IsStrOrder.
Module Type UsualDecStrOrder := UsualStrOrder <+ HasCompare.
Module Type UsualOrderedType <: UsualDecidableType <: OrderedType
 := UsualDecStrOrder <+ HasEqDec.
Module Type UsualOrderedTypeFull := UsualOrderedType <+ HasLe <+ LeIsLtEq.

(** NB: in [UsualOrderedType], the field [lt_compat] is
    useless since [eq] is [Leibniz], but it should be
    there for subtyping. *)

Module Type UsualStrOrder' := UsualStrOrder <+ LtNotation.
Module Type UsualDecStrOrder' := UsualDecStrOrder <+ LtNotation.
Module Type UsualOrderedType' := UsualOrderedType <+ LtNotation.
Module Type UsualOrderedTypeFull' := UsualOrderedTypeFull <+ LtLeNotation.

(** * Purely logical versions *)

Module Type LtIsTotal (Import E:EqLt').
  Axiom lt_total : forall x y, x<y \/ x==y \/ y<x.
End LtIsTotal.

Module Type TotalOrder := StrOrder <+ HasLe <+ LeIsLtEq <+ LtIsTotal.
Module Type UsualTotalOrder <: TotalOrder
 := UsualStrOrder <+ HasLe <+ LeIsLtEq <+ LtIsTotal.

Module Type TotalOrder' := TotalOrder <+ EqLtLeNotation.
Module Type UsualTotalOrder' := UsualTotalOrder <+ LtLeNotation.

(** * Conversions *)

(** From [compare] to [eqb], and then [eq_dec] *)

Module Compare2EqBool (Import O:DecStrOrder') <: HasEqBool O.

 Definition eqb x y :=
   match compare x y with Eq => true | _ => false end.

 Lemma eqb_eq : forall x y, eqb x y = true <-> x==y.
 Proof.
 unfold eqb. intros x y.
 destruct (compare_spec x y) as [H|H|H]; split; auto; try discriminate.
 intros EQ; rewrite EQ in H; elim (StrictOrder_Irreflexive _ H).
 intros EQ; rewrite EQ in H; elim (StrictOrder_Irreflexive _ H).
 Qed.

End Compare2EqBool.

Module DSO_to_OT (O:DecStrOrder) <: OrderedType :=
  O <+ Compare2EqBool <+ HasEqBool2Dec.

(** From [OrderedType] To [OrderedTypeFull] (adding [<=]) *)

Module OT_to_Full (O:OrderedType') <: OrderedTypeFull.
 Include O.
 Definition le x y := x<y \/ x==y.
 Lemma le_lteq : forall x y, le x y <-> x<y \/ x==y.
 Proof. unfold le; split; auto. Qed.
End OT_to_Full.

(** From computational to logical versions *)

Module OTF_LtIsTotal (Import O:OrderedTypeFull') <: LtIsTotal O.
 Lemma lt_total : forall x y, x<y \/ x==y \/ y<x.
 Proof. intros; destruct (compare_spec x y); auto. Qed.
End OTF_LtIsTotal.

Module OTF_to_TotalOrder (O:OrderedTypeFull) <: TotalOrder
 := O <+ OTF_LtIsTotal.


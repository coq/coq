(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export Relations Morphisms Setoid Equalities.
Set Implicit Arguments.
Unset Strict Implicit.

(** * Ordered types *)

(** First, signatures with only the order relations *)

Module Type HasLt (Import T:Typ).
  Parameter Inline(40) lt : t -> t -> Prop.
End HasLt.

Module Type HasLe (Import T:Typ).
  Parameter Inline(40) le : t -> t -> Prop.
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

Module Type StrOrder := EqualityType <+ HasLt <+ IsStrOrder.
Module Type StrOrder' := StrOrder <+ EqLtNotation.

(** Versions with a decidable ternary comparison *)

Module Type HasCmp (Import T:Typ).
  Parameter Inline compare : t -> t -> comparison.
End HasCmp.

Module Type CmpNotation (T:Typ)(C:HasCmp T).
  Infix "?=" := C.compare (at level 70, no associativity).
End CmpNotation.

Module Type CmpSpec (Import E:EqLt')(Import C:HasCmp E).
  Axiom compare_spec : forall x y, CompareSpec (x==y) (x<y) (y<x) (compare x y).
End CmpSpec.

Module Type HasCompare (E:EqLt) := HasCmp E <+ CmpSpec E.

Module Type DecStrOrder := StrOrder <+ HasCompare.
Module Type DecStrOrder' := DecStrOrder <+ EqLtNotation <+ CmpNotation.

Module Type OrderedType <: DecidableType := DecStrOrder <+ HasEqDec.
Module Type OrderedType' := OrderedType <+ EqLtNotation <+ CmpNotation.

Module Type OrderedTypeFull := OrderedType <+ HasLe <+ LeIsLtEq.
Module Type OrderedTypeFull' :=
 OrderedTypeFull <+ EqLtLeNotation <+ CmpNotation.

(** NB: in [OrderedType], an [eq_dec] could be deduced from [compare].
  But adding this redundant field allows seeing an [OrderedType] as a
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


(** * Versions with boolean comparisons

    This style is used in [Mergesort]
*)

(** For stating properties like transitivity  of [leb],
    we coerce [bool] into [Prop]. *)

Local Coercion is_true : bool >-> Sortclass.
Hint Unfold is_true.

Module Type HasLeb (Import T:Typ).
 Parameter Inline leb : t -> t -> bool.
End HasLeb.

Module Type HasLtb (Import T:Typ).
 Parameter Inline ltb : t -> t -> bool.
End HasLtb.

Module Type LebNotation (T:Typ)(E:HasLeb T).
 Infix "<=?" := E.leb (at level 35).
End LebNotation.

Module Type LtbNotation (T:Typ)(E:HasLtb T).
 Infix "<?" := E.ltb (at level 35).
End LtbNotation.

Module Type LebSpec (T:Typ)(X:HasLe T)(Y:HasLeb T).
 Parameter leb_le : forall x y, Y.leb x y = true <-> X.le x y.
End LebSpec.

Module Type LtbSpec (T:Typ)(X:HasLt T)(Y:HasLtb T).
 Parameter ltb_lt : forall x y, Y.ltb x y = true <-> X.lt x y.
End LtbSpec.

Module Type LeBool := Typ <+ HasLeb.
Module Type LtBool := Typ <+ HasLtb.
Module Type LeBool' := LeBool <+ LebNotation.
Module Type LtBool' := LtBool <+ LtbNotation.

Module Type LebIsTotal (Import X:LeBool').
 Axiom leb_total : forall x y, (x <=? y) = true \/ (y <=? x) = true.
End LebIsTotal.

Module Type TotalLeBool := LeBool <+ LebIsTotal.
Module Type TotalLeBool' := LeBool' <+ LebIsTotal.

Module Type LebIsTransitive (Import X:LeBool').
 Axiom leb_trans : Transitive X.leb.
End LebIsTransitive.

Module Type TotalTransitiveLeBool := TotalLeBool <+ LebIsTransitive.
Module Type TotalTransitiveLeBool' := TotalLeBool' <+ LebIsTransitive.

(** Grouping all boolean comparison functions *)

Module Type HasBoolOrdFuns (T:Typ) := HasEqb T <+ HasLtb T <+ HasLeb T.

Module Type HasBoolOrdFuns' (T:Typ) :=
 HasBoolOrdFuns T <+ EqbNotation T <+ LtbNotation T <+ LebNotation T.

Module Type BoolOrdSpecs (O:EqLtLe)(F:HasBoolOrdFuns O) :=
 EqbSpec O O F <+ LtbSpec O O F <+ LebSpec O O F.

Module Type OrderFunctions (E:EqLtLe) :=
  HasCompare E <+ HasBoolOrdFuns E <+ BoolOrdSpecs E.
Module Type OrderFunctions' (E:EqLtLe) :=
  HasCompare E <+ CmpNotation E <+ HasBoolOrdFuns' E <+ BoolOrdSpecs E.

(** * From [OrderedTypeFull] to [TotalTransitiveLeBool] *)

Module OTF_to_TTLB (Import O : OrderedTypeFull') <: TotalTransitiveLeBool.

 Definition leb x y :=
  match compare x y with Gt => false | _ => true end.

 Lemma leb_le : forall x y, leb x y <-> x <= y.
 Proof.
 intros. unfold leb. rewrite le_lteq.
 destruct (compare_spec x y) as [EQ|LT|GT]; split; auto.
 discriminate.
 intros LE. elim (StrictOrder_Irreflexive x).
 destruct LE as [LT|EQ]. now transitivity y. now rewrite <- EQ in GT.
 Qed.

 Lemma leb_total : forall x y, leb x y \/ leb y x.
 Proof.
 intros. rewrite 2 leb_le. rewrite 2 le_lteq.
 destruct (compare_spec x y); intuition.
 Qed.

 Lemma leb_trans : Transitive leb.
 Proof.
 intros x y z. rewrite !leb_le, !le_lteq.
 intros [Hxy|Hxy] [Hyz|Hyz].
 left; transitivity y; auto.
 left; rewrite <- Hyz; auto.
 left; rewrite Hxy; auto.
 right; transitivity y; auto.
 Qed.

 Definition t := t.

End OTF_to_TTLB.


(** * From [TotalTransitiveLeBool] to [OrderedTypeFull]

    [le] is [leb ... = true].
    [eq] is [le /\ swap le].
    [lt] is [le /\ ~swap le].
*)

Local Open Scope bool_scope.

Module TTLB_to_OTF (Import O : TotalTransitiveLeBool') <: OrderedTypeFull.

 Definition t := t.

 Definition le x y : Prop := x <=? y.
 Definition eq x y : Prop := le x y /\ le y x.
 Definition lt x y : Prop := le x y /\ ~le y x.

 Definition compare x y :=
  if x <=? y then (if y <=? x then Eq else Lt) else Gt.

 Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
 Proof.
 intros. unfold compare.
 case_eq (x <=? y).
 case_eq (y <=? x).
 constructor. split; auto.
 constructor. split; congruence.
 constructor. destruct (leb_total x y); split; congruence.
 Qed.

 Definition eqb x y := (x <=? y) && (y <=? x).

 Lemma eqb_eq : forall x y, eqb x y <-> eq x y.
 Proof.
 intros. unfold eq, eqb, le.
 case leb; simpl; intuition; discriminate.
 Qed.

 Include HasEqBool2Dec.

 Instance eq_equiv : Equivalence eq.
 Proof.
 split.
 intros x; unfold eq, le. destruct (leb_total x x); auto.
 intros x y; unfold eq, le. intuition.
 intros x y z; unfold eq, le. intuition; apply leb_trans with y; auto.
 Qed.

 Instance lt_strorder : StrictOrder lt.
 Proof.
 split.
 intros x. unfold lt; red; intuition.
 intros x y z; unfold lt, le. intuition.
 apply leb_trans with y; auto.
 absurd (z <=? y); auto.
 apply leb_trans with x; auto.
 Qed.

 Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
 Proof.
 apply proper_sym_impl_iff_2; auto with *.
 intros x x' Hx y y' Hy' H. unfold eq, lt, le in *.
 intuition.
 apply leb_trans with x; auto.
 apply leb_trans with y; auto.
 absurd (y <=? x); auto.
 apply leb_trans with x'; auto.
 apply leb_trans with y'; auto.
 Qed.

 Definition le_lteq : forall x y, le x y <-> lt x y \/ eq x y.
 Proof.
 intros.
 unfold lt, eq, le.
 split; [ | intuition ].
 intros LE.
 case_eq (y <=? x); [right|left]; intuition; try discriminate.
 Qed.

End TTLB_to_OTF.

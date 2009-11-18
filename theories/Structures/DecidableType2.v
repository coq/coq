(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

Require Export RelationClasses.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Types with Equality, and nothing more (for subtyping purpose) *)

Module Type BareEquality.
  Parameter Inline t : Type.
  Parameter Inline eq : t -> t -> Prop.
End BareEquality.

(** * Specification of the equality by the Type Classe [Equivalence] *)

Module Type IsEq (Import E:BareEquality).
  Instance eq_equiv : Equivalence eq.
  Hint Resolve (@Equivalence_Reflexive _ _ eq_equiv).
  Hint Resolve (@Equivalence_Transitive _ _ eq_equiv).
  Hint Immediate (@Equivalence_Symmetric _ _ eq_equiv).
End IsEq.

(** * Earlier specification of equality by three separate lemmas. *)

Module Type IsEqOrig (Import E:BareEquality).
  Axiom eq_refl : forall x : t, eq x x.
  Axiom eq_sym : forall x y : t, eq x y -> eq y x.
  Axiom eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Hint Immediate eq_sym.
  Hint Resolve eq_refl eq_trans.
End IsEqOrig.

(** * Types with decidable equality *)

Module Type HasEqDec (Import E:BareEquality).
  Parameter eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
End HasEqDec.

(** * Boolean Equality *)

(** Having [eq_dec] is the same as having a boolean equality plus
    a correctness proof. *)

Module Type HasEqBool (Import E:BareEquality).
  Parameter Inline eqb : t -> t -> bool.
  Parameter eqb_eq : forall x y, eqb x y = true <-> eq x y.
End HasEqBool.

(** From these basic blocks, we can build many combinations
    of static standalone module types. *)

Module Type EqualityType := BareEquality <+ IsEq.

Module Type EqualityTypeOrig := BareEquality <+ IsEqOrig.

Module Type EqualityTypeBoth <: EqualityType <: EqualityTypeOrig
 := BareEquality <+ IsEq <+ IsEqOrig.

Module Type DecidableType <: EqualityType
 := BareEquality <+ IsEq <+ HasEqDec.

Module Type DecidableTypeOrig <: EqualityTypeOrig
 := BareEquality <+ IsEqOrig <+ HasEqDec.

Module Type DecidableTypeBoth <: DecidableType <: DecidableTypeOrig
 := EqualityTypeBoth <+ HasEqDec.

Module Type BooleanEqualityType <: EqualityType
 := BareEquality <+ IsEq <+ HasEqBool.

Module Type BooleanDecidableType <: DecidableType <: BooleanEqualityType
 := BareEquality <+ IsEq <+ HasEqDec <+ HasEqBool.

Module Type DecidableTypeFull <: DecidableTypeBoth <: BooleanDecidableType
 := BareEquality <+ IsEq <+ IsEqOrig <+ HasEqDec <+ HasEqBool.


(** * Compatibility wrapper from/to the old version of
      [EqualityType] and [DecidableType] *)

Module BackportEq (E:BareEquality)(F:IsEq E) <: IsEqOrig E.
 Definition eq_refl := @Equivalence_Reflexive _ _ F.eq_equiv.
 Definition eq_sym := @Equivalence_Symmetric _ _ F.eq_equiv.
 Definition eq_trans := @Equivalence_Transitive _ _ F.eq_equiv.
End BackportEq.

Module UpdateEq (E:BareEquality)(F:IsEqOrig E) <: IsEq E.
 Instance eq_equiv : Equivalence E.eq.
 Proof. exact (Build_Equivalence _ _ F.eq_refl F.eq_sym F.eq_trans). Qed.
End UpdateEq.

Module Backport_ET (E:EqualityType) <: EqualityTypeBoth
 := E <+ BackportEq E E.

Module Update_ET (E:EqualityTypeOrig) <: EqualityTypeBoth
 := E <+ UpdateEq E E.

Module Backport_DT (E:DecidableType) <: DecidableTypeBoth
 := E <+ BackportEq E E.

Module Update_DT (E:DecidableTypeOrig) <: DecidableTypeBoth
 := E <+ UpdateEq E E.


(** * Having [eq_dec] is equivalent to having [eqb] and its spec. *)

Module HasEqDec2Bool (E:BareEquality)(F:HasEqDec E) <: HasEqBool E.
 Definition eqb x y := if F.eq_dec x y then true else false.
 Lemma eqb_eq : forall x y, eqb x y = true <-> E.eq x y.
 Proof.
  intros x y. unfold eqb. destruct F.eq_dec as [EQ|NEQ].
  auto with *.
  split. discriminate. intro EQ; elim NEQ; auto.
 Qed.
End HasEqDec2Bool.

Module HasEqBool2Dec (E:BareEquality)(F:HasEqBool E) <: HasEqDec E.
 Lemma eq_dec : forall x y, {E.eq x y}+{~E.eq x y}.
 Proof.
  intros x y. assert (H:=F.eqb_eq x y).
  destruct (F.eqb x y); [left|right].
  apply -> H; auto.
  intro EQ. apply H in EQ. discriminate.
 Defined.
End HasEqBool2Dec.

Module Dec2Bool (E:DecidableType) <: BooleanDecidableType
 := E <+ HasEqDec2Bool E E.

Module Bool2Dec (E:BooleanEqualityType) <: BooleanDecidableType
 := E <+ HasEqBool2Dec E E.



(** * UsualDecidableType

   A particular case of [DecidableType] where the equality is
   the usual one of Coq. *)

Module Type UsualBareEquality <: BareEquality.
 Parameter Inline t : Type.
 Definition eq := @eq t.
End UsualBareEquality.

Module UsualIsEq (E:UsualBareEquality) <: IsEq E.
 Program Instance eq_equiv : Equivalence E.eq.
End UsualIsEq.

Module UsualIsEqOrig (E:UsualBareEquality) <: IsEqOrig E.
 Definition eq_refl := @eq_refl E.t.
 Definition eq_sym := @eq_sym E.t.
 Definition eq_trans := @eq_trans E.t.
End UsualIsEqOrig.

Module Type UsualEqualityType <: EqualityType
 := UsualBareEquality <+ IsEq.

Module Type UsualDecidableType <: DecidableType
 := UsualBareEquality <+ IsEq <+ HasEqDec.

Module Type UsualDecidableTypeBoth <: DecidableTypeBoth
 := UsualBareEquality <+ IsEq <+ IsEqOrig <+ HasEqDec.

Module Type UsualBoolEq := UsualBareEquality <+ HasEqBool.

Module Type UsualDecidableTypeFull <: DecidableTypeFull
 := UsualBareEquality <+ IsEq <+ IsEqOrig <+ HasEqDec <+ HasEqBool.


(** Some shortcuts for easily building a [UsualDecidableType] *)

Module Type MiniDecidableType.
 Parameter t : Type.
 Parameter eq_dec : forall x y : t, {eq x y}+{~eq x y}.
End MiniDecidableType.

Module Make_UDT (M:MiniDecidableType) <: UsualDecidableTypeBoth.
 Definition eq := @eq M.t.
 Include M <+ UsualIsEq <+ UsualIsEqOrig.
End Make_UDT.

Module Make_UDTF (M:UsualBoolEq) <: UsualDecidableTypeFull
 := M <+ UsualIsEq <+ UsualIsEqOrig <+ HasEqBool2Dec.

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

Module Type Equality_fun (Import E:BareEquality).
  Instance eq_equiv : Equivalence eq.
  Hint Resolve (@Equivalence_Reflexive _ _ eq_equiv).
  Hint Resolve (@Equivalence_Transitive _ _ eq_equiv).
  Hint Immediate (@Equivalence_Symmetric _ _ eq_equiv).
End Equality_fun.

(** * Earlier specification of equality by three separate lemmas. *)

Module Type EqualityOrig_fun(Import E:BareEquality).
  Axiom eq_refl : forall x : t, eq x x.
  Axiom eq_sym : forall x y : t, eq x y -> eq y x.
  Axiom eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Hint Immediate eq_sym.
  Hint Resolve eq_refl eq_trans.
End EqualityOrig_fun.

(** * Types with decidable equality *)

Module Type Decidable_fun (Import E:BareEquality).
  Parameter eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
End Decidable_fun.

(** * Boolean Equality *)

(** Having [eq_dec] is the same as having a boolean equality plus
    a correctness proof. *)

Module Type BoolEq_fun (Import E:BareEquality).
  Parameter Inline eqb : t -> t -> bool.
  Parameter eqb_eq : forall x y, eqb x y = true <-> eq x y.
End BoolEq_fun.

(** From these basic blocks, we can build many combinations
    of static standalone module types. *)

Module Type EqualityType.
  Include Type BareEquality.
  Include Self Type Equality_fun.
End EqualityType.

Module Type EqualityTypeOrig.
  Include Type BareEquality.
  Include Self Type EqualityOrig_fun.
End EqualityTypeOrig.

Module Type EqualityTypeBoth. (* <: EqualityType <: EqualityTypeOrig *)
  Include Type BareEquality.
  Include Self Type Equality_fun.
  Include Self Type EqualityOrig_fun.
End EqualityTypeBoth.

Module Type DecidableType. (* <: EqualityType *)
  Include Type BareEquality.
  Include Self Type Equality_fun.
  Include Self Type Decidable_fun.
End DecidableType.

Module Type DecidableTypeOrig. (* <: EqualityTypeOrig *)
  Include Type BareEquality.
  Include Self Type EqualityOrig_fun.
  Include Self Type Decidable_fun.
End DecidableTypeOrig.

Module Type DecidableTypeBoth. (* <: DecidableType <: DecidableTypeOrig *)
  Include Type EqualityTypeBoth.
  Include Self Type Decidable_fun.
End DecidableTypeBoth.

Module Type BooleanEqualityType. (* <: EqualityType *)
  Include Type BareEquality.
  Include Self Type Equality_fun.
  Include Self Type BoolEq_fun.
End BooleanEqualityType.

Module Type BooleanDecidableType. (* <: DecidableType <: BooleanEqualityType *)
  Include Type BareEquality.
  Include Self Type Equality_fun.
  Include Self Type Decidable_fun.
  Include Self Type BoolEq_fun.
End BooleanDecidableType.

Module Type DecidableTypeFull. (* <: all previous interfaces *)
  Include Type BareEquality.
  Include Self Type Equality_fun.
  Include Self Type EqualityOrig_fun.
  Include Self Type Decidable_fun.
  Include Self Type BoolEq_fun.
End DecidableTypeFull.


(** * Compatibility wrapper from/to the old version of
      [EqualityType] and [DecidableType] *)

Module Backport_ET_fun (E:BareEquality)(F:Equality_fun E) <: EqualityOrig_fun E.
 Definition eq_refl := @Equivalence_Reflexive _ _ F.eq_equiv.
 Definition eq_sym := @Equivalence_Symmetric _ _ F.eq_equiv.
 Definition eq_trans := @Equivalence_Transitive _ _ F.eq_equiv.
End Backport_ET_fun.

Module Update_ET_fun (E:BareEquality)(F:EqualityOrig_fun E) <: Equality_fun E.
 Instance eq_equiv : Equivalence E.eq.
 Proof. exact (Build_Equivalence _ _ F.eq_refl F.eq_sym F.eq_trans). Qed.
End Update_ET_fun.

Module Backport_ET (E:EqualityType) <: EqualityTypeBoth.
 Include E.
 Include Backport_ET_fun E E.
End Backport_ET.

Module Update_ET (E:EqualityTypeOrig) <: EqualityTypeBoth.
 Include E.
 Include Update_ET_fun E E.
End Update_ET.

Module Backport_DT (E:DecidableType) <: DecidableTypeBoth.
 Include E.
 Include Backport_ET_fun E E.
End Backport_DT.

Module Update_DT (E:DecidableTypeOrig) <: DecidableTypeBoth.
 Include E.
 Include Update_ET_fun E E.
End Update_DT.


(** * Having [eq_dec] is equivalent to having [eqb] and its spec. *)

Module Dec2Bool_fun (E:BareEquality)(F:Decidable_fun E) <: BoolEq_fun E.
 Definition eqb x y := if F.eq_dec x y then true else false.
 Lemma eqb_eq : forall x y, eqb x y = true <-> E.eq x y.
 Proof.
  intros x y. unfold eqb. destruct F.eq_dec as [EQ|NEQ].
  auto with *.
  split. discriminate. intro EQ; elim NEQ; auto.
 Qed.
End Dec2Bool_fun.

Module Bool2Dec_fun (E:BareEquality)(F:BoolEq_fun E) <: Decidable_fun E.
 Lemma eq_dec : forall x y, {E.eq x y}+{~E.eq x y}.
 Proof.
  intros x y. assert (H:=F.eqb_eq x y).
  destruct (F.eqb x y); [left|right].
  apply -> H; auto.
  intro EQ. apply H in EQ. discriminate.
 Defined.
End Bool2Dec_fun.

Module Dec2Bool (E:DecidableType) <: BooleanDecidableType.
 Include E.
 Include Dec2Bool_fun E E.
End Dec2Bool.

Module Bool2Dec (E:BooleanEqualityType) <: BooleanDecidableType.
 Include E.
 Include Bool2Dec_fun E E.
End Bool2Dec.



(** * UsualDecidableType

   A particular case of [DecidableType] where the equality is
   the usual one of Coq. *)

Module Type UsualBareEquality. (* <: BareEquality *)
 Parameter Inline t : Type.
 Definition eq := @eq t.
End UsualBareEquality.

Module UsualEquality_fun (E:UsualBareEquality) <: Equality_fun E.
 Program Instance eq_equiv : Equivalence E.eq.
End UsualEquality_fun.

Module UsualEqualityOrig_fun (E:UsualBareEquality) <: EqualityOrig_fun E.
 Definition eq_refl := @eq_refl E.t.
 Definition eq_sym := @eq_sym E.t.
 Definition eq_trans := @eq_trans E.t.
End UsualEqualityOrig_fun.

Module Type UsualEqualityType. (* <: EqualityType *)
 Include Type UsualBareEquality.
 Include Self Type Equality_fun.
End UsualEqualityType.

Module Type UsualDecidableType. (* <: DecidableType *)
 Include Type UsualBareEquality.
 Include Self Type Equality_fun.
 Include Self Type Decidable_fun.
End UsualDecidableType.

Module Type UsualDecidableTypeBoth. (* <: DecidableTypeBoth *)
 Include Type UsualBareEquality.
 Include Self Type Equality_fun.
 Include Self Type EqualityOrig_fun.
 Include Self Type Decidable_fun.
End UsualDecidableTypeBoth.

Module Type UsualBoolEq.
 Include Type UsualBareEquality.
 Include Self Type BoolEq_fun.
End UsualBoolEq.

Module Type UsualDecidableTypeFull. (* <: DecidableTypeFull *)
 Include Type UsualBareEquality.
 Include Self Type Equality_fun.
 Include Self Type EqualityOrig_fun.
 Include Self Type Decidable_fun.
 Include Self Type BoolEq_fun.
End UsualDecidableTypeFull.

(** a [UsualDecidableType] is in particular an [DecidableType]. *)

Module UDT_to_DT (U:UsualDecidableType) <: DecidableType := U.

(** Some shortcuts for easily building a UsualDecidableType *)

Module Type MiniDecidableType.
 Parameter t : Type.
 Parameter eq_dec : forall x y : t, {eq x y}+{~eq x y}.
End MiniDecidableType.

Module Make_UDT (M:MiniDecidableType) <: UsualDecidableTypeBoth.
 Include M.
 Definition eq := @eq M.t.
 Include Self UsualEquality_fun.
 Include Self UsualEqualityOrig_fun.
End Make_UDT.

Module Make_UDTF (M:UsualBoolEq) <: UsualDecidableTypeFull.
 Include M. (* t, eq, eqb, eqb_eq *)
 Include UsualEquality_fun M.
 Include UsualEqualityOrig_fun M.
 Include Bool2Dec_fun M M.
End Make_UDTF.


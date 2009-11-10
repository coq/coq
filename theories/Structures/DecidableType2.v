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

Module Type EqualityType.
  Parameter Inline t : Type.
  Parameter Inline eq : t -> t -> Prop.
  Instance eq_equiv : Equivalence eq.

  Hint Resolve (@Equivalence_Reflexive _ _ eq_equiv).
  Hint Resolve (@Equivalence_Transitive _ _ eq_equiv).
  Hint Immediate (@Equivalence_Symmetric _ _ eq_equiv).
End EqualityType.

(** * Types with decidable Equality (but no ordering) *)

Module Type DecidableType.
  Include Type EqualityType.
  Parameter eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
End DecidableType.

(** * Old versions of [DecidableType], with reflexivity, symmetry,
  transitivity as three separate axioms. *)

Module Type EqualityTypeOrig.
  Parameter Inline t : Type.
  Parameter Inline eq : t -> t -> Prop.

  Axiom eq_refl : forall x : t, eq x x.
  Axiom eq_sym : forall x y : t, eq x y -> eq y x.
  Axiom eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.

  Hint Immediate eq_sym.
  Hint Resolve eq_refl eq_trans.
End EqualityTypeOrig.

Module Type DecidableTypeOrig.
  Include Type EqualityTypeOrig.
  Parameter eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
End DecidableTypeOrig.

(** * Compatibility wrapper from/to the old version of [DecidableType] *)

(** Interestingly, a module can be at the same time a [DecidableType]
    and a [DecidableTypeOrig]. For the sake of compatibility,
    this will be the case of all [DecidableType] modules provided here.
*)

Module Backport_ET (E:EqualityType) <: EqualityTypeOrig.
 Include E.
 Definition eq_refl := @Equivalence_Reflexive _ _ eq_equiv.
 Definition eq_sym := @Equivalence_Symmetric _ _ eq_equiv.
 Definition eq_trans := @Equivalence_Transitive _ _ eq_equiv.
End Backport_ET.

Module Update_ET (E:EqualityTypeOrig) <: EqualityType.
 Include E.
 Instance eq_equiv : Equivalence eq.
 Proof. exact (Build_Equivalence _ _ eq_refl eq_sym eq_trans). Qed.
End Update_ET.

Module Backport_DT (E:DecidableType) <: DecidableTypeOrig.
 Include Backport_ET E.
 Definition eq_dec := E.eq_dec.
End Backport_DT.

Module Update_DT (E:DecidableTypeOrig) <: DecidableType.
 Include Update_ET E.
 Definition eq_dec := E.eq_dec.
End Update_DT.


(** * UsualDecidableType

   A particular case of [DecidableType] where the equality is
   the usual one of Coq. *)

Module Type UsualDecidableType.
 Parameter Inline t : Type.
 Definition eq := @eq t.
 Program Instance eq_equiv : Equivalence eq.
 Parameter eq_dec : forall x y, { eq x y }+{~eq x y }.
End UsualDecidableType.

(** a [UsualDecidableType] is in particular an [DecidableType]. *)

Module UDT_to_DT (U:UsualDecidableType) <: DecidableType := U.

(** an shortcut for easily building a UsualDecidableType *)

Module Type MiniDecidableType.
 Parameter Inline t : Type.
 Parameter eq_dec : forall x y:t, { x=y }+{ x<>y }.
End MiniDecidableType.

Module Make_UDT (M:MiniDecidableType) <: UsualDecidableType.
 Definition t:=M.t.
 Definition eq := @eq M.t.
 Program Instance eq_equiv : Equivalence eq.
 Definition eq_dec := M.eq_dec.
 (* For building DecidableTypeOrig at the same time: *)
 Definition eq_refl := @Equivalence_Reflexive _ _ eq_equiv.
 Definition eq_sym := @Equivalence_Symmetric _ _ eq_equiv.
 Definition eq_trans := @Equivalence_Transitive _ _ eq_equiv.
End Make_UDT.


(** * Boolean Equality *)

(** Having [eq_dec] is the same as having a boolean equality plus
    a correctness proof. *)

Module Type BooleanEqualityType.
 Include Type EqualityType.
 Parameter Inline eqb : t -> t -> bool.
 Parameter eqb_eq : forall x y, eqb x y = true <-> eq x y.
End BooleanEqualityType.

Module Bool_to_Dec (E:BooleanEqualityType) <: DecidableType.
 Include E.
 Lemma eq_dec : forall x y, {eq x y}+{~eq x y}.
 Proof.
  intros x y. assert (H:=eqb_eq x y).
  destruct (eqb x y); [left|right].
  apply -> H; auto.
  intro EQ. apply H in EQ. discriminate.
 Defined.
End Bool_to_Dec.

Module Dec_to_Bool (E:DecidableType) <: BooleanEqualityType.
 Include E.
 Definition eqb x y := if eq_dec x y then true else false.
 Lemma eqb_eq : forall x y, eqb x y = true <-> eq x y.
 Proof.
  intros x y. unfold eqb. destruct eq_dec as [EQ|NEQ].
  auto with *.
  split. discriminate. intro EQ; elim NEQ; auto.
 Qed.
End Dec_to_Bool.

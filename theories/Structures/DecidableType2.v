(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

Require Export SetoidList.
Require DecidableType. (* No Import here, this is on purpose *)

Set Implicit Arguments.
Unset Strict Implicit.

(** * Types with Equalities, and nothing more (for subtyping purpose) *)

Module Type EqualityType.
  Parameter Inline t : Type.
  Parameter Inline eq : t -> t -> Prop.
  Instance eq_equiv : Equivalence eq.

  Hint Resolve (@Equivalence_Reflexive _ _ eq_equiv).
  Hint Resolve (@Equivalence_Transitive _ _ eq_equiv).
  Hint Immediate (@Equivalence_Symmetric _ _ eq_equiv).
End EqualityType.

(** * Types with decidable Equalities (but no ordering) *)

Module Type DecidableType.
  Include Type EqualityType.
  Parameter eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
End DecidableType.

(** * Compatibility wrapper from/to the old version of [DecidableType] *)

Module Type DecidableTypeOrig := DecidableType.DecidableType.

Module Backport_DT (E:DecidableType) <: DecidableTypeOrig.
 Include E.
 Definition eq_refl := @Equivalence_Reflexive _ _ eq_equiv.
 Definition eq_sym := @Equivalence_Symmetric _ _ eq_equiv.
 Definition eq_trans := @Equivalence_Transitive _ _ eq_equiv.
End Backport_DT.

Module Update_DT (E:DecidableTypeOrig) <: DecidableType.
 Include E.
 Instance eq_equiv : Equivalence eq.
 Proof. exact (Build_Equivalence _ _ eq_refl eq_sym eq_trans). Qed.
End Update_DT.


(** * Additional notions about keys and datas used in FMap *)

Module KeyDecidableType(D:DecidableType).
 Import D.

 Section Elt.
 Variable elt : Type.
 Notation key:=t.

  Definition eqk (p p':key*elt) := eq (fst p) (fst p').
  Definition eqke (p p':key*elt) :=
          eq (fst p) (fst p') /\ (snd p) = (snd p').

  Global Hint Unfold eqk eqke.
  Global Hint Extern 2 (eqke ?a ?b) => split.

   (* eqke is stricter than eqk *)

   Lemma eqke_eqk : forall x x', eqke x x' -> eqk x x'.
   Proof.
     unfold eqk, eqke; intuition.
   Qed.

  (* eqk, eqke are equalities *)

  Instance eqk_equiv : Equivalence eqk.
  Proof.
   constructor; eauto.
  Qed.

  Instance eqke_equiv : Equivalence eqke.
  Proof.
   constructor. auto.
   red; unfold eqke; intuition.
   red; unfold eqke; intuition; [ eauto | congruence ].
  Qed.

  Global Hint Resolve (@Equivalence_Reflexive _ _ eqk_equiv).
  Global Hint Resolve (@Equivalence_Transitive _ _ eqk_equiv).
  Global Hint Immediate (@Equivalence_Symmetric _ _ eqk_equiv).
  Global Hint Resolve (@Equivalence_Reflexive _ _ eqke_equiv).
  Global Hint Resolve (@Equivalence_Transitive _ _ eqke_equiv).
  Global Hint Immediate (@Equivalence_Symmetric _ _ eqke_equiv).

  Lemma InA_eqke_eqk :
     forall x m, InA eqke x m -> InA eqk x m.
  Proof.
    unfold eqke; induction 1; intuition.
  Qed.
  Global Hint Resolve InA_eqke_eqk.

  Lemma InA_eqk : forall p q m, eqk p q -> InA eqk p m -> InA eqk q m.
  Proof.
   intros. rewrite <- H; auto.
  Qed.

  Definition MapsTo (k:key)(e:elt):= InA eqke (k,e).
  Definition In k m := exists e:elt, MapsTo k e m.

  Global Hint Unfold MapsTo In.

  (* An alternative formulation for [In k l] is [exists e, InA eqk (k,e) l] *)

  Lemma In_alt : forall k l, In k l <-> exists e, InA eqk (k,e) l.
  Proof.
  firstorder.
  exists x; auto.
  induction H.
  destruct y.
  exists e; auto.
  destruct IHInA as [e H0].
  exists e; auto.
  Qed.

  Global Instance MapsTo_compat :
    Proper (eq==>Logic.eq==>Logic.eq==>iff) MapsTo.
  Proof.
  intros x x' Hxx' e e' Hee' l l' Hll'; subst.
  unfold MapsTo.
  assert (EQN : eqke (x,e') (x',e')) by (compute;auto).
  rewrite EQN; intuition.
  Qed.

  Lemma MapsTo_eq : forall l x y e, eq x y -> MapsTo x e l -> MapsTo y e l.
  Proof.
  intros; rewrite <- H; auto.
  Qed.

  Global Instance In_compat : Proper (eq==>Logic.eq==>iff) In.
  Proof.
  intros x x' Hxx' l l' Hll'; subst l.
  unfold In.
  split; intros (e,He); exists e.
  rewrite <- Hxx'; auto.
  rewrite Hxx'; auto.
  Qed.

  Lemma In_eq : forall l x y, eq x y -> In x l -> In y l.
  Proof.
  intros; rewrite <- H; auto.
  Qed.

  Lemma In_inv : forall k k' e l, In k ((k',e) :: l) -> eq k k' \/ In k l.
  Proof.
    inversion 1.
    inversion_clear H0; eauto.
    destruct H1; simpl in *; intuition.
  Qed.

  Lemma In_inv_2 : forall k k' e e' l,
      InA eqk (k, e) ((k', e') :: l) -> ~ eq k k' -> InA eqk (k, e) l.
  Proof.
   inversion_clear 1; compute in H0; intuition.
  Qed.

  Lemma In_inv_3 : forall x x' l,
      InA eqke x (x' :: l) -> ~ eqk x x' -> InA eqke x l.
  Proof.
   inversion_clear 1; compute in H0; intuition.
  Qed.

 End Elt.

 Hint Resolve In_inv_2 In_inv_3.

End KeyDecidableType.






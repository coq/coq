(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export SetoidList.
Require Equalities.

Set Implicit Arguments.
Unset Strict Implicit.

(** NB: This file is here only for compatibility with earlier version of
    [FSets] and [FMap]. Please use [Structures/Equalities.v] directly now. *)

(** * Types with Equalities, and nothing more (for subtyping purpose) *)

Module Type EqualityType := Equalities.EqualityTypeOrig.

(** * Types with decidable Equalities (but no ordering) *)

Module Type DecidableType := Equalities.DecidableTypeOrig.

(** * Additional notions about keys and datas used in FMap *)

Module KeyDecidableType(D:DecidableType).
 Import D.

 Section Elt.
 Variable elt : Type.
 Notation key:=t.

  Definition eqk (p p':key*elt) := eq (fst p) (fst p').
  Definition eqke (p p':key*elt) :=
          eq (fst p) (fst p') /\ (snd p) = (snd p').

  Hint Unfold eqk eqke.
  Hint Extern 2 (eqke ?a ?b) => split.

   (* eqke is stricter than eqk *)

   Lemma eqke_eqk : forall x x', eqke x x' -> eqk x x'.
   Proof.
     unfold eqk, eqke; intuition.
   Qed.

  (* eqk, eqke are equalities *)

  Lemma eqk_refl : forall e, eqk e e.
  Proof. auto. Qed.

  Lemma eqke_refl : forall e, eqke e e.
  Proof. auto. Qed.

  Lemma eqk_sym : forall e e', eqk e e' -> eqk e' e.
  Proof. auto. Qed.

  Lemma eqke_sym : forall e e', eqke e e' -> eqke e' e.
  Proof. unfold eqke; intuition. Qed.

  Lemma eqk_trans : forall e e' e'', eqk e e' -> eqk e' e'' -> eqk e e''.
  Proof. eauto. Qed.

  Lemma eqke_trans : forall e e' e'', eqke e e' -> eqke e' e'' -> eqke e e''.
  Proof.
    unfold eqke; intuition; [ eauto | congruence ].
  Qed.

  Hint Resolve eqk_trans eqke_trans eqk_refl eqke_refl.
  Hint Immediate eqk_sym eqke_sym.

  Global Instance eqk_equiv : Equivalence eqk.
  Proof. split; eauto. Qed.

  Global Instance eqke_equiv : Equivalence eqke.
  Proof. split; eauto. Qed.

  Lemma InA_eqke_eqk :
     forall x m, InA eqke x m -> InA eqk x m.
  Proof.
    unfold eqke; induction 1; intuition. 
  Qed.
  Hint Resolve InA_eqke_eqk.

  Lemma InA_eqk : forall p q m, eqk p q -> InA eqk p m -> InA eqk q m.
  Proof.
   intros; apply InA_eqA with p; auto using eqk_equiv.
  Qed.

  Definition MapsTo (k:key)(e:elt):= InA eqke (k,e).
  Definition In k m := exists e:elt, MapsTo k e m.

  Hint Unfold MapsTo In.

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

  Lemma MapsTo_eq : forall l x y e, eq x y -> MapsTo x e l -> MapsTo y e l.
  Proof.
    intros; unfold MapsTo in *; apply InA_eqA with (x,e); auto using eqke_equiv.
  Qed.

  Lemma In_eq : forall l x y, eq x y -> In x l -> In y l.
  Proof.
  destruct 2 as (e,E); exists e; eapply MapsTo_eq; eauto.
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

 Hint Unfold eqk eqke.
 Hint Extern 2 (eqke ?a ?b) => split.
 Hint Resolve eqk_trans eqke_trans eqk_refl eqke_refl.
 Hint Immediate eqk_sym eqke_sym.
 Hint Resolve InA_eqke_eqk.
 Hint Unfold MapsTo In.
 Hint Resolve In_inv_2 In_inv_3.

End KeyDecidableType.






(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Equalities Bool SetoidList RelationPairs.

Set Implicit Arguments.

(** * Keys and datas used in the future MMaps *)

Module KeyDecidableType(D:DecidableType).

 Local Open Scope signature_scope.
 Local Notation key := D.t.

 Definition eqk {elt} : relation (key*elt) := D.eq @@1.
 Definition eqke {elt} : relation (key*elt) := D.eq * Logic.eq.

 Hint Unfold eqk eqke.

 (** eqk, eqke are equalities *)

 Instance eqk_equiv {elt} : Equivalence (@eqk elt) := _.

 Instance eqke_equiv {elt} : Equivalence (@eqke elt) := _.

 (** eqke is stricter than eqk *)

 Instance eqke_eqk {elt} : subrelation (@eqke elt) (@eqk elt).
 Proof. firstorder. Qed.

 (** Alternative definitions of eqke and eqk *)

 Lemma eqke_def {elt} k k' (e e':elt) :
  eqke (k,e) (k',e') = (D.eq k k' /\ e = e').
 Proof. reflexivity. Defined.

 Lemma eqke_def' {elt} (p q:key*elt) :
  eqke p q = (D.eq (fst p) (fst q) /\ snd p = snd q).
 Proof. reflexivity. Defined.

 Lemma eqke_1 {elt} k k' (e e':elt) : eqke (k,e) (k',e') -> D.eq k k'.
 Proof. now destruct 1. Qed.

 Lemma eqke_2 {elt} k k' (e e':elt) : eqke (k,e) (k',e') -> e=e'.
 Proof. now destruct 1. Qed.

 Lemma eqk_def {elt} k k' (e e':elt) : eqk (k,e) (k',e') = D.eq k k'.
 Proof. reflexivity. Defined.

 Lemma eqk_def' {elt} (p q:key*elt) : eqk p q = D.eq (fst p) (fst q).
 Proof. reflexivity. Qed.

 Lemma eqk_1 {elt} k k' (e e':elt) : eqk (k,e) (k',e') -> D.eq k k'.
 Proof. trivial. Qed.

 Hint Resolve eqke_1 eqke_2 eqk_1.

 (* Additional facts *)

 Lemma InA_eqke_eqk {elt} p (m:list (key*elt)) :
   InA eqke p m -> InA eqk p m.
 Proof.
  induction 1; firstorder.
 Qed.
 Hint Resolve InA_eqke_eqk.

 Lemma InA_eqk_eqke {elt} p (m:list (key*elt)) :
  InA eqk p m -> exists q, eqk p q /\ InA eqke q m.
 Proof.
  induction 1; firstorder.
 Qed.

 Lemma InA_eqk {elt} p q (m:list (key*elt)) :
   eqk p q -> InA eqk p m -> InA eqk q m.
 Proof.
  now intros <-.
 Qed.

 Definition MapsTo {elt} (k:key)(e:elt):= InA eqke (k,e).
 Definition In {elt} k m := exists e:elt, MapsTo k e m.

 Hint Unfold MapsTo In.

 (* Alternative formulations for [In k l] *)

 Lemma In_alt {elt} k (l:list (key*elt)) :
   In k l <-> exists e, InA eqk (k,e) l.
 Proof.
  unfold In, MapsTo.
  split; intros (e,H).
  - exists e; auto.
  - apply InA_eqk_eqke in H. destruct H as ((k',e'),(E,H)).
    compute in E. exists e'. now rewrite E.
 Qed.

 Lemma In_alt' {elt} (l:list (key*elt)) k e :
   In k l <-> InA eqk (k,e) l.
 Proof.
  rewrite In_alt. firstorder. eapply InA_eqk; eauto. now compute.
 Qed.

 Lemma In_alt2 {elt} k (l:list (key*elt)) :
   In k l <-> Exists (fun p => D.eq k (fst p)) l.
 Proof.
  unfold In, MapsTo.
  setoid_rewrite Exists_exists; setoid_rewrite InA_alt.
  firstorder.
  exists (snd x), x; auto.
 Qed.

 Lemma In_nil {elt} k : In k (@nil (key*elt)) <-> False.
 Proof.
  rewrite In_alt2; apply Exists_nil.
 Qed.

 Lemma In_cons {elt} k p (l:list (key*elt)) :
   In k (p::l) <-> D.eq k (fst p) \/ In k l.
 Proof.
  rewrite !In_alt2, Exists_cons; intuition.
 Qed.

 Instance MapsTo_compat {elt} :
   Proper (D.eq==>Logic.eq==>equivlistA eqke==>iff) (@MapsTo elt).
 Proof.
  intros x x' Hx e e' He l l' Hl. unfold MapsTo.
  rewrite Hx, He, Hl; intuition.
 Qed.

 Instance In_compat {elt} : Proper (D.eq==>equivlistA eqk==>iff) (@In elt).
 Proof.
  intros x x' Hx l l' Hl. rewrite !In_alt.
  setoid_rewrite Hl. setoid_rewrite Hx. intuition.
 Qed.

 Lemma MapsTo_eq {elt} (l:list (key*elt)) x y e :
   D.eq x y -> MapsTo x e l -> MapsTo y e l.
 Proof. now intros <-. Qed.

 Lemma In_eq {elt} (l:list (key*elt)) x y :
   D.eq x y -> In x l -> In y l.
 Proof. now intros <-. Qed.

 Lemma In_inv {elt} k k' e (l:list (key*elt)) :
   In k ((k',e) :: l) -> D.eq k k' \/ In k l.
 Proof.
  intros (e',H). red in H. rewrite InA_cons, eqke_def in H.
  intuition. right. now exists e'.
 Qed.

 Lemma In_inv_2 {elt} k k' e e' (l:list (key*elt)) :
   InA eqk (k, e) ((k', e') :: l) -> ~ D.eq k k' -> InA eqk (k, e) l.
 Proof.
  rewrite InA_cons, eqk_def. intuition.
 Qed.

 Lemma In_inv_3 {elt} x x' (l:list (key*elt)) :
   InA eqke x (x' :: l) -> ~ eqk x x' -> InA eqke x l.
 Proof.
  rewrite InA_cons. destruct 1 as [H|H]; trivial. destruct 1.
  eauto with *.
 Qed.

 Hint Extern 2 (eqke ?a ?b) => split.
 Hint Resolve InA_eqke_eqk.
 Hint Resolve In_inv_2 In_inv_3.

End KeyDecidableType.


(** * PairDecidableType

   From two decidable types, we can build a new DecidableType
   over their cartesian product. *)

Module PairDecidableType(D1 D2:DecidableType) <: DecidableType.

 Definition t := (D1.t * D2.t)%type.

 Definition eq := (D1.eq * D2.eq)%signature.

 Instance eq_equiv : Equivalence eq := _.

 Definition eq_dec : forall x y, { eq x y }+{ ~eq x y }.
 Proof.
 intros (x1,x2) (y1,y2); unfold eq; simpl.
 destruct (D1.eq_dec x1 y1); destruct (D2.eq_dec x2 y2);
  compute; intuition.
 Defined.

End PairDecidableType.

(** Similarly for pairs of UsualDecidableType *)

Module PairUsualDecidableType(D1 D2:UsualDecidableType) <: UsualDecidableType.
 Definition t := (D1.t * D2.t)%type.
 Definition eq := @eq t.
 Instance eq_equiv : Equivalence eq := _.
 Definition eq_dec : forall x y, { eq x y }+{ ~eq x y }.
 Proof.
 intros (x1,x2) (y1,y2);
 destruct (D1.eq_dec x1 y1); destruct (D2.eq_dec x2 y2);
 unfold eq, D1.eq, D2.eq in *; simpl;
 (left; f_equal; auto; fail) ||
 (right; intros [=]; auto).
 Defined.

End PairUsualDecidableType.

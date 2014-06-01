(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

Require Import Equalities Bool SetoidList RelationPairs.

(** * Keys and datas used in FMap *)

Module KeyDecidableType(Import D:DecidableType).

 Section Elt.
 Variable elt : Type.
 Notation key:=t.

  Local Open Scope signature_scope.

  Definition eqk : relation (key*elt) := eq @@1.
  Definition eqke : relation (key*elt) := eq * Logic.eq.
  Hint Unfold eqk eqke.

  (* eqke is stricter than eqk *)

  Global Instance eqke_eqk : subrelation eqke eqk.
  Proof. firstorder. Qed.

  (* eqk, eqke are equalities, ltk is a strict order *)

  Global Instance eqk_equiv : Equivalence eqk := _.

  Global Instance eqke_equiv : Equivalence eqke := _.

  (* Additionnal facts *)

  Lemma InA_eqke_eqk :
     forall x m, InA eqke x m -> InA eqk x m.
  Proof.
    unfold eqke, RelProd; induction 1; firstorder.
  Qed.
  Hint Resolve InA_eqke_eqk.

  Lemma InA_eqk : forall p q m, eqk p q -> InA eqk p m -> InA eqk q m.
  Proof.
   intros. rewrite <- H; auto.
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
  destruct y; compute in H.
  exists e; left; auto.
  destruct IHInA as [e H0].
  exists e; auto.
  Qed.

  Lemma In_alt2 : forall k l, In k l <-> Exists (fun p => eq k (fst p)) l.
  Proof.
  unfold In, MapsTo.
  setoid_rewrite Exists_exists; setoid_rewrite InA_alt.
  firstorder.
  exists (snd x), x; auto.
  Qed.

  Lemma In_nil : forall k, In k nil <-> False.
  Proof.
  intros; rewrite In_alt2; apply Exists_nil.
  Qed.

  Lemma In_cons : forall k p l,
   In k (p::l) <-> eq k (fst p) \/ In k l.
  Proof.
  intros; rewrite !In_alt2, Exists_cons; intuition.
  Qed.

  Global Instance MapsTo_compat :
   Proper (eq==>Logic.eq==>equivlistA eqke==>iff) MapsTo.
  Proof.
  intros x x' Hx e e' He l l' Hl. unfold MapsTo.
  rewrite Hx, He, Hl; intuition.
  Qed.

  Global Instance In_compat : Proper (eq==>equivlistA eqk==>iff) In.
  Proof.
  intros x x' Hx l l' Hl. rewrite !In_alt.
  setoid_rewrite Hl. setoid_rewrite Hx. intuition.
  Qed.

  Lemma MapsTo_eq : forall l x y e, eq x y -> MapsTo x e l -> MapsTo y e l.
  Proof. intros l x y e EQ. rewrite <- EQ; auto. Qed.

  Lemma In_eq : forall l x y, eq x y -> In x l -> In y l.
  Proof. intros l x y EQ. rewrite <- EQ; auto. Qed.

  Lemma In_inv : forall k k' e l, In k ((k',e) :: l) -> eq k k' \/ In k l.
  Proof.
    intros; invlist In; invlist MapsTo. compute in * |- ; intuition.
    right; exists x; auto.
  Qed.

  Lemma In_inv_2 : forall k k' e e' l,
      InA eqk (k, e) ((k', e') :: l) -> ~ eq k k' -> InA eqk (k, e) l.
  Proof.
   intros; invlist InA; intuition.
  Qed.

  Lemma In_inv_3 : forall x x' l,
      InA eqke x (x' :: l) -> ~ eqk x x' -> InA eqke x l.
  Proof.
   intros; invlist InA; compute in * |- ; intuition.
  Qed.

 End Elt.

 Hint Unfold eqk eqke.
 Hint Extern 2 (eqke ?a ?b) => split.
 Hint Resolve InA_eqke_eqk.
 Hint Unfold MapsTo In.
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

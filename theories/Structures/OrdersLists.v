(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

Require Export RelationPairs SetoidList Orders.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Specialization of results about lists modulo. *)

Module OrderedTypeLists (Import O:OrderedType).

Section ForNotations.

Notation In:=(InA eq).
Notation Inf:=(lelistA lt).
Notation Sort:=(sort lt).
Notation NoDup:=(NoDupA eq).

Lemma In_eq : forall l x y, eq x y -> In x l -> In y l.
Proof. intros. rewrite <- H; auto. Qed.

Lemma ListIn_In : forall l x, List.In x l -> In x l.
Proof. exact (In_InA eq_equiv). Qed.

Lemma Inf_lt : forall l x y, lt x y -> Inf y l -> Inf x l.
Proof. exact (InfA_ltA lt_strorder). Qed.

Lemma Inf_eq : forall l x y, eq x y -> Inf y l -> Inf x l.
Proof. exact (InfA_eqA eq_equiv lt_strorder lt_compat). Qed.

Lemma Sort_Inf_In : forall l x a, Sort l -> Inf a l -> In x l -> lt a x.
Proof. exact (SortA_InfA_InA eq_equiv lt_strorder lt_compat). Qed.

Lemma ListIn_Inf : forall l x, (forall y, List.In y l -> lt x y) -> Inf x l.
Proof. exact (@In_InfA t lt). Qed.

Lemma In_Inf : forall l x, (forall y, In y l -> lt x y) -> Inf x l.
Proof. exact (InA_InfA eq_equiv (ltA:=lt)). Qed.

Lemma Inf_alt :
 forall l x, Sort l -> (Inf x l <-> (forall y, In y l -> lt x y)).
Proof. exact (InfA_alt eq_equiv lt_strorder lt_compat). Qed.

Lemma Sort_NoDup : forall l, Sort l -> NoDup l.
Proof. exact (SortA_NoDupA eq_equiv lt_strorder lt_compat) . Qed.

End ForNotations.

Hint Resolve ListIn_In Sort_NoDup Inf_lt.
Hint Immediate In_eq Inf_lt.

End OrderedTypeLists.





(** * Results about keys and data as manipulated in FMaps. *)


Module KeyOrderedType(Import O:OrderedType).
 Module Import MO:=OrderedTypeLists(O).

 Section Elt.
 Variable elt : Type.
 Notation key:=t.

  Local Open Scope signature_scope.

  Definition eqk : relation (key*elt) := eq @@1.
  Definition eqke : relation (key*elt) := eq * Logic.eq.
  Definition ltk : relation (key*elt) := lt @@1.

  Hint Unfold eqk eqke ltk.

  (* eqke is stricter than eqk *)

  Global Instance eqke_eqk : subrelation eqke eqk.
  Proof. firstorder. Qed.

  (* eqk, eqke are equalities, ltk is a strict order *)

  Global Instance eqk_equiv : Equivalence eqk := _.

  Global Instance eqke_equiv : Equivalence eqke := _.

  Global Instance ltk_strorder : StrictOrder ltk := _.

  Global Instance ltk_compat : Proper (eqk==>eqk==>iff) ltk.
  Proof. unfold eqk, ltk; auto with *. Qed.

  (* Additionnal facts *)

  Global Instance pair_compat : Proper (eq==>Logic.eq==>eqke) (@pair key elt).
  Proof. apply pair_compat. Qed.

  Lemma ltk_not_eqk : forall e e', ltk e e' -> ~ eqk e e'.
  Proof.
  intros e e' LT EQ; rewrite EQ in LT.
  elim (StrictOrder_Irreflexive _ LT).
  Qed.

  Lemma ltk_not_eqke : forall e e', ltk e e' -> ~eqke e e'.
  Proof.
  intros e e' LT EQ; rewrite EQ in LT.
  elim (StrictOrder_Irreflexive _ LT).
  Qed.

  Lemma InA_eqke_eqk :
     forall x m, InA eqke x m -> InA eqk x m.
  Proof.
    unfold eqke, RelProd; induction 1; firstorder.
  Qed.
  Hint Resolve InA_eqke_eqk.

  Definition MapsTo (k:key)(e:elt):= InA eqke (k,e).
  Definition In k m := exists e:elt, MapsTo k e m.
  Notation Sort := (sort ltk).
  Notation Inf := (lelistA ltk).

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

  Lemma Inf_eq : forall l x x', eqk x x' -> Inf x' l -> Inf x l.
  Proof. intros l x x' H. rewrite H; auto. Qed.

  Lemma Inf_lt : forall l x x', ltk x x' -> Inf x' l -> Inf x l.
  Proof. apply InfA_ltA; auto with *. Qed.

  Hint Immediate Inf_eq.
  Hint Resolve Inf_lt.

  Lemma Sort_Inf_In :
      forall l p q, Sort l -> Inf q l -> InA eqk p l -> ltk q p.
  Proof. apply SortA_InfA_InA; auto with *. Qed.

  Lemma Sort_Inf_NotIn :
      forall l k e, Sort l -> Inf (k,e) l ->  ~In k l.
  Proof.
    intros; red; intros.
    destruct H1 as [e' H2].
    elim (@ltk_not_eqk (k,e) (k,e')).
    eapply Sort_Inf_In; eauto.
    repeat red; reflexivity.
  Qed.

  Lemma Sort_NoDupA: forall l, Sort l -> NoDupA eqk l.
  Proof. apply SortA_NoDupA; auto with *. Qed.

  Lemma Sort_In_cons_1 : forall e l e', Sort (e::l) -> InA eqk e' l -> ltk e e'.
  Proof.
   intros; invlist sort; eapply Sort_Inf_In; eauto.
  Qed.

  Lemma Sort_In_cons_2 : forall l e e', Sort (e::l) -> InA eqk e' (e::l) ->
      ltk e e' \/ eqk e e'.
  Proof.
    intros; invlist InA; auto with relations.
    left; apply Sort_In_cons_1 with l; auto with relations.
  Qed.

  Lemma Sort_In_cons_3 :
    forall x l k e, Sort ((k,e)::l) -> In x l -> ~eq x k.
  Proof.
    intros; invlist sort; red; intros.
    eapply Sort_Inf_NotIn; eauto using In_eq.
  Qed.

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

 Hint Unfold eqk eqke ltk.
 Hint Extern 2 (eqke ?a ?b) => split.
 Hint Resolve ltk_not_eqk ltk_not_eqke.
 Hint Resolve InA_eqke_eqk.
 Hint Unfold MapsTo In.
 Hint Immediate Inf_eq.
 Hint Resolve Inf_lt.
 Hint Resolve Sort_Inf_NotIn.
 Hint Resolve In_inv_2 In_inv_3.

End KeyOrderedType.


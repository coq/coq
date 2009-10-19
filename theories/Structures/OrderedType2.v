(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

Require Export SetoidList DecidableType2 OrderTac.
Set Implicit Arguments.
Unset Strict Implicit.

(** * Ordered types *)

Definition Cmp (A:Type)(eq lt : relation A) c :=
 match c with
  | Eq => eq
  | Lt => lt
  | Gt => flip lt
 end.

Module Type MiniOrderedType.
  Include Type EqualityType.

  Parameter Inline lt : t -> t -> Prop.
  Instance lt_strorder : StrictOrder lt.
  Instance lt_compat : Proper (eq==>eq==>iff) lt.

  Parameter compare : t -> t -> comparison.
  Axiom compare_spec : forall x y, Cmp eq lt (compare x y) x y.

End MiniOrderedType.

Module Type OrderedType.
  Include Type MiniOrderedType.

  (** A [eq_dec] can be deduced from [compare] below. But adding this
     redundant field allows to see an OrderedType as a DecidableType. *)
  Parameter eq_dec : forall x y, { eq x y } + { ~ eq x y }.

End OrderedType.

Module MOT_to_OT (Import O : MiniOrderedType) <: OrderedType.
  Include O.

  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
   intros.
   generalize (compare_spec x y); destruct (compare x y);
    unfold Cmp, flip; intros.
    left; auto.
    right. intro H'; rewrite <- H' in H.
      apply (StrictOrder_Irreflexive x); auto.
    right. intro H'; rewrite <- H' in H.
      apply (StrictOrder_Irreflexive x); auto.
  Defined.

End MOT_to_OT.

(** * Ordered types properties *)

(** Additional properties that can be derived from signature
    [OrderedType]. *)

Module OrderedTypeFacts (Import O: OrderedType).

  Infix "==" := eq (at level 70, no associativity) : order.
  Infix "<" := lt : order.
  Notation "x <= y" := (~lt y x) : order.
  Infix "?=" := compare (at level 70, no associativity) : order.

  Local Open Scope order.

  Ltac elim_compare x y :=
   generalize (compare_spec x y); destruct (compare x y);
   unfold Cmp, flip.

  Module OrderElts : OrderTacSig
    with Definition t := t
    with Definition eq := eq
    with Definition lt := lt.
  (* Opaque signature is crucial for ltac to work correctly later *)
  Include O.
  Definition le x y := x<y \/ x==y.
  Lemma lt_total : forall x y, x<y \/ x==y \/ y<x.
  Proof. intros; elim_compare x y; intuition. Qed.
  Lemma le_lteq : forall x y, le x y <-> lt x y \/ eq x y.
  Proof. unfold le; intuition. Qed.
  End OrderElts.
  Module OrderTac := MakeOrderTac OrderElts.

  Ltac order :=
    change eq with OrderElts.eq in *;
    change lt with OrderElts.lt in *;
    OrderTac.order.

  (** The following lemmas are either re-phrasing of [eq_equiv] and
      [lt_strorder] or immediately provable by [order]. Interest:
      compatibility, test of order, etc *)

  Definition eq_refl (x:t) : x==x := Equivalence_Reflexive x.

  Definition eq_sym (x y:t) : x==y -> y==x := Equivalence_Symmetric x y.

  Definition eq_trans (x y z:t) : x==y -> y==z -> x==z :=
   Equivalence_Transitive x y z.

  Definition lt_trans (x y z:t) : x<y -> y<z -> x<z :=
   StrictOrder_Transitive x y z.

  Definition lt_irrefl (x:t) : ~x<x := StrictOrder_Irreflexive x.

  (** Some more about [compare] *)

  Lemma compare_eq_iff : forall x y, (x ?= y) = Eq <-> x==y.
  Proof.
   intros; elim_compare x y; intuition; try discriminate; order.
  Qed.

  Lemma compare_lt_iff : forall x y, (x ?= y) = Lt <-> x<y.
  Proof.
   intros; elim_compare x y; intuition; try discriminate; order.
  Qed.

  Lemma compare_gt_iff : forall x y, (x ?= y) = Gt <-> y<x.
  Proof.
   intros; elim_compare x y; intuition; try discriminate; order.
  Qed.

  Lemma compare_ge_iff : forall x y, (x ?= y) <> Lt <-> y<=x.
  Proof.
   intros; rewrite compare_lt_iff; intuition.
  Qed.

  Lemma compare_le_iff : forall x y, (x ?= y) <> Gt <-> x<=y.
  Proof.
   intros; rewrite compare_gt_iff; intuition.
  Qed.

  Hint Rewrite compare_eq_iff compare_lt_iff compare_gt_iff : order.

  Instance compare_compat : Proper (eq==>eq==>Logic.eq) compare.
  Proof.
  intros x x' Hxx' y y' Hyy'.
  elim_compare x' y'; intros; autorewrite with order; order.
  Qed.

  Lemma compare_refl : forall x, (x ?= x) = Eq.
  Proof.
   intros; elim_compare x x; auto; order.
  Qed.

  Lemma compare_antisym : forall x y, (y ?= x) = CompOpp (x ?= y).
  Proof.
   intros; elim_compare x y; simpl; intros; autorewrite with order; order.
  Qed.

  (** For compatibility reasons *)
  Definition eq_dec := eq_dec.

  Lemma lt_dec : forall x y : t, {lt x y} + {~ lt x y}.
  Proof.
   intros; elim_compare x y; [ right | left | right ]; order.
  Defined.

  Definition eqb x y : bool := if eq_dec x y then true else false.

  Lemma if_eq_dec : forall x y (B:Type)(b b':B),
    (if eq_dec x y then b else b') =
    (match compare x y with Eq => b | _ => b' end).
  Proof.
  intros; destruct eq_dec; elim_compare x y; auto; order.
  Qed.

  Lemma eqb_alt :
    forall x y, eqb x y = match compare x y with Eq => true | _ => false end.
  Proof.
  unfold eqb; intros; apply if_eq_dec.
  Qed.

  Instance eqb_compat : Proper (eq==>eq==>Logic.eq) eqb.
  Proof.
  intros x x' Hxx' y y' Hyy'.
  rewrite 2 eqb_alt, Hxx', Hyy'; auto.
  Qed.


(* Specialization of resuts about lists modulo. *)

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

End OrderedTypeFacts.


(** Some tests of [order] : is it at least capable of
    proving some basic properties ? *)

Module OrderedTypeTest (O:OrderedType).
  Module Import MO := OrderedTypeFacts O.
  Local Open Scope order.
  Lemma lt_not_eq x y : x<y -> ~x==y.  Proof. order. Qed.
  Lemma lt_eq x y z : x<y -> y==z -> x<z. Proof. order. Qed.
  Lemma eq_lt x y z : x==y -> y<z -> x<z. Proof. order. Qed.
  Lemma le_eq x y z : x<=y -> y==z -> x<=z. Proof. order. Qed.
  Lemma eq_le x y z : x==y -> y<=z -> x<=z. Proof. order. Qed.
  Lemma neq_eq x y z : ~x==y -> y==z -> ~x==z. Proof. order. Qed.
  Lemma eq_neq x y z : x==y -> ~y==z -> ~x==z. Proof. order. Qed.
  Lemma le_lt_trans x y z : x<=y -> y<z -> x<z. Proof. order. Qed.
  Lemma lt_le_trans x y z : x<y -> y<=z -> x<z. Proof. order. Qed.
  Lemma le_trans x y z : x<=y -> y<=z -> x<=z. Proof. order. Qed.
  Lemma le_antisym x y : x<=y -> y<=x -> x==y. Proof. order. Qed.
  Lemma le_neq x y : x<=y -> ~x==y -> x<y. Proof. order. Qed.
  Lemma neq_sym x y : ~x==y -> ~y==x. Proof. order. Qed.
  Lemma lt_le x y : x<y -> x<=y. Proof. order. Qed.
  Lemma gt_not_eq x y : y<x -> ~x==y. Proof. order. Qed.
  Lemma eq_not_lt x y : x==y -> ~x<y. Proof. order. Qed.
  Lemma eq_not_gt x y : x==y -> ~ y<x. Proof. order. Qed.
  Lemma lt_not_gt x y : x<y -> ~ y<x. Proof. order. Qed.
End OrderedTypeTest.


(** * Relations over pairs (TO MIGRATE in some TypeClasses file) *)

Definition ProdRel {A B}(RA:relation A)(RB:relation B) : relation (A*B) :=
 fun p p' => RA (fst p) (fst p') /\ RB (snd p) (snd p').

Definition FstRel {A B}(R:relation A) : relation (A*B) :=
 fun p p' => R (fst p) (fst p').

Definition SndRel {A B}(R:relation B) : relation (A*B) :=
 fun p p' => R (snd p) (snd p').

Instance ProdRel_equiv {A B} `(Equivalence A RA)`(Equivalence B RB) :
 Equivalence (ProdRel RA RB).
Proof. firstorder. Qed.

Instance FstRel_equiv {A B} `(Equivalence A RA) :
 Equivalence (FstRel RA (B:=B)).
Proof. firstorder. Qed.

Instance SndRel_equiv {A B} `(Equivalence B RB) :
 Equivalence (SndRel RB (A:=A)).
Proof. firstorder. Qed.

Instance FstRel_strorder {A B} `(StrictOrder A RA) :
 StrictOrder (FstRel RA (B:=B)).
Proof. firstorder. Qed.

Instance SndRel_strorder {A B} `(StrictOrder B RB) :
 StrictOrder (SndRel RB (A:=A)).
Proof. firstorder. Qed.

Lemma FstRel_ProdRel {A B}(RA:relation A) : forall p p':A*B,
 (FstRel RA) p p' <-> (ProdRel RA (fun _ _ =>True)) p p'.
Proof. firstorder. Qed.

Lemma SndRel_ProdRel {A B}(RB:relation B) : forall p p':A*B,
 (SndRel RB) p p' <-> (ProdRel (fun _ _ =>True) RB) p p'.
Proof. firstorder. Qed.

Lemma ProdRel_alt {A B}(RA:relation A)(RB:relation B) : forall p p':A*B,
 (ProdRel RA RB) p p' <-> relation_conjunction (FstRel RA) (SndRel RB) p p'.
Proof. firstorder. Qed.

Instance FstRel_compat {A B} (R : relation A)`(Proper _ (Ri==>Ri==>Ro) R) :
 Proper (FstRel Ri==>FstRel Ri==>Ro) (FstRel R (B:=B)).
Proof.
 intros A B R Ri Ro H (a1,b1) (a1',b1') Hab1 (a2,b2) (a2',b2') Hab2.
 unfold FstRel in *; simpl in *. apply H; auto.
Qed.

Instance SndRel_compat {A B} (R : relation B)`(Proper _ (Ri==>Ri==>Ro) R) :
 Proper (SndRel Ri==>SndRel Ri==>Ro) (SndRel R (A:=A)).
Proof.
 intros A B R Ri Ro H (a1,b1) (a1',b1') Hab1 (a2,b2) (a2',b2') Hab2.
 unfold SndRel in *; simpl in *. apply H; auto.
Qed.

Instance FstRel_sub {A B} (RA:relation A)(RB:relation B):
 subrelation (ProdRel RA RB) (FstRel RA).
Proof. firstorder. Qed.

Instance SndRel_sub {A B} (RA:relation A)(RB:relation B):
 subrelation (ProdRel RA RB) (SndRel RB).
Proof. firstorder. Qed.

Instance pair_compat { A B } (RA:relation A)(RB : relation B) :
 Proper (RA==>RB==>ProdRel RA RB) (@pair A B).
Proof. firstorder. Qed.


Hint Unfold ProdRel FstRel SndRel.
Hint Extern 2 (ProdRel _ _ _ _) => split.


Module KeyOrderedType(Import O:OrderedType).
 Module Import MO:=OrderedTypeFacts(O).

 Section Elt.
 Variable elt : Type.
 Notation key:=t.

  Definition eqk : relation (key*elt) := FstRel eq.
  Definition eqke : relation (key*elt) := ProdRel eq Logic.eq.
  Definition ltk : relation (key*elt) := FstRel lt.

  Hint Unfold eqk eqke ltk.

  (* eqke is stricter than eqk *)

  Global Instance eqke_eqk : subrelation eqke eqk.
  Proof. unfold eqke, eqk; auto with *. Qed.

  (* eqk, eqke are equalities, ltk is a strict order *)

  Global Instance eqk_equiv : Equivalence eqk.

  Global Instance eqke_equiv : Equivalence eqke.

  Global Instance ltk_strorder : StrictOrder ltk.

  Global Instance ltk_compat : Proper (eqk==>eqk==>iff) ltk.
  Proof. unfold eqk, ltk; auto with *. Qed.

  (* Additionnal facts *)

  Global Instance pair_compat : Proper (eq==>Logic.eq==>eqke) (@pair key elt).
  Proof. unfold eqke; auto with *. Qed.

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
    unfold eqke, ProdRel; induction 1; intuition.
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
  exists e; auto.
  destruct IHInA as [e H0].
  exists e; auto.
  Qed.

  Lemma In_alt2 : forall k l, In k l <-> ExistsL (fun p => eq k (fst p)) l.
  Proof.
  unfold In, MapsTo.
  setoid_rewrite ExistsL_exists; setoid_rewrite InA_alt.
  firstorder.
  exists (snd x), x; auto.
  Qed.

  Lemma In_nil : forall k, In k nil <-> False.
  Proof.
  intros; rewrite In_alt2; apply ExistsL_nil.
  Qed.

  Lemma In_cons : forall k p l,
   In k (p::l) <-> eq k (fst p) \/ In k l.
  Proof.
  intros; rewrite !In_alt2, ExistsL_cons; intuition.
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
    red; simpl; auto.
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
    intros; invlist InA; auto.
    left; apply Sort_In_cons_1 with l; auto.
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

 Hint Resolve (fun elt => @Equivalence_Reflexive _ _ (eqk_equiv elt)).
 Hint Resolve (fun elt => @Equivalence_Transitive _ _ (eqk_equiv elt)).
 Hint Immediate (fun elt => @Equivalence_Symmetric _ _ (eqk_equiv elt)).
 Hint Resolve (fun elt => @Equivalence_Reflexive _ _ (eqke_equiv elt)).
 Hint Resolve (fun elt => @Equivalence_Transitive _ _ (eqke_equiv elt)).
 Hint Immediate (fun elt => @Equivalence_Symmetric _ _ (eqke_equiv elt)).
 Hint Resolve (fun elt => @StrictOrder_Transitive _ _ (ltk_strorder elt)).

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


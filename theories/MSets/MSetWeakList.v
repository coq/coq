(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Finite sets library *)

(** This file proposes an implementation of the non-dependent
    interface [MSetWeakInterface.S] using lists without redundancy. *)

Require Import MSetInterface.
Set Implicit Arguments.
Unset Strict Implicit.

(** * Functions over lists

   First, we provide sets as lists which are (morally) without redundancy.
   The specs are proved under the additional condition of no redundancy.
   And the functions returning sets are proved to preserve this invariant. *)


(** ** The set operations. *)

Module Ops (X: DecidableType) <: WOps X.

  Definition elt := X.t.
  Definition t := list elt.

  Definition empty : t := nil.

  Definition is_empty (l : t) : bool := if l then true else false.

  Fixpoint mem (x : elt) (s : t) : bool :=
    match s with
    | nil => false
    | y :: l =>
           if X.eq_dec x y then true else mem x l
    end.

  Fixpoint add (x : elt) (s : t) : t :=
    match s with
    | nil => x :: nil
    | y :: l =>
        if X.eq_dec x y then s else y :: add x l
    end.

  Definition singleton (x : elt) : t := x :: nil.

  Fixpoint remove (x : elt) (s : t) : t :=
    match s with
    | nil => nil
    | y :: l =>
        if X.eq_dec x y then l else y :: remove x l
    end.

  Definition fold (B : Type) (f : elt -> B -> B) : t -> B -> B :=
    fold_left (flip f).

  Definition union (s : t) : t -> t := fold add s.

  Definition diff (s s' : t) : t := fold remove s' s.

  Definition inter (s s': t) : t :=
    fold (fun x s => if mem x s' then add x s else s) s nil.

  Definition subset (s s' : t) : bool := is_empty (diff s s').

  Definition equal (s s' : t) : bool := andb (subset s s') (subset s' s).

  Fixpoint filter (f : elt -> bool) (s : t) : t :=
    match s with
    | nil => nil
    | x :: l => if f x then x :: filter f l else filter f l
    end.

  Fixpoint for_all (f : elt -> bool) (s : t) : bool :=
    match s with
    | nil => true
    | x :: l => if f x then for_all f l else false
    end.

  Fixpoint exists_ (f : elt -> bool) (s : t) : bool :=
    match s with
    | nil => false
    | x :: l => if f x then true else exists_ f l
    end.

  Fixpoint partition (f : elt -> bool) (s : t) : t * t :=
    match s with
    | nil => (nil, nil)
    | x :: l =>
        let (s1, s2) := partition f l in
        if f x then (x :: s1, s2) else (s1, x :: s2)
    end.

  Definition cardinal (s : t) : nat := length s.

  Definition elements (s : t) : list elt := s.

  Definition choose (s : t) : option elt :=
     match s with
      | nil => None
      | x::_ => Some x
     end.

End Ops.

(** ** Proofs of set operation specifications. *)

Module MakeRaw (X:DecidableType) <: WRawSets X.
  Include Ops X.

  Section ForNotations.
  Notation NoDup := (NoDupA X.eq).
  Notation In := (InA X.eq).

  (* TODO: modify proofs in order to avoid these hints *)
  Let eqr:= (@Equivalence_Reflexive _ _ X.eq_equiv).
  Let eqsym:= (@Equivalence_Symmetric _ _ X.eq_equiv).
  Let eqtrans:= (@Equivalence_Transitive _ _ X.eq_equiv).
  Hint Resolve eqr eqtrans.
  Hint Immediate eqsym.

  Definition IsOk := NoDup.

  Class Ok (s:t) : Prop := ok : NoDup s.

  Hint Unfold Ok.
  Hint Resolve ok.

  Instance NoDup_Ok s (nd : NoDup s) : Ok s := { ok := nd }.

  Ltac inv_ok := match goal with
   | H:Ok (_ :: _) |- _ => inversion_clear H; inv_ok
   | H:Ok nil |- _ => clear H; inv_ok
   | H:NoDup ?l |- _ => change (Ok l) in H; inv_ok
   | _ => idtac
  end.

  Ltac inv := invlist InA; inv_ok.
  Ltac constructors := repeat constructor.

  Fixpoint isok l := match l with
   | nil => true
   | a::l => negb (mem a l) && isok l
  end.

  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.

  Lemma In_compat : Proper (X.eq==>eq==>iff) In.
  Proof.
  repeat red; intros. subst. rewrite H; auto.
  Qed.

  Lemma mem_spec : forall s x `{Ok s},
   mem x s = true <-> In x s.
  Proof.
  induction s; intros.
  split; intros; inv. discriminate.
  simpl; destruct (X.eq_dec x a); split; intros; inv; auto.
  right; rewrite <- IHs; auto.
  rewrite IHs; auto.
  Qed.

  Lemma isok_iff : forall l, Ok l <-> isok l = true.
  Proof.
  induction l.
  intuition.
  simpl.
  rewrite andb_true_iff.
  rewrite negb_true_iff.
  rewrite <- IHl.
  split; intros H. inv.
  split; auto.
  apply not_true_is_false. rewrite mem_spec; auto.
  destruct H; constructors; auto.
  rewrite <- mem_spec; auto; congruence.
  Qed.

  Global Instance isok_Ok l : isok l = true -> Ok l | 10.
  Proof.
  intros. apply <- isok_iff; auto.
  Qed.

  Lemma add_spec :
   forall (s : t) (x y : elt) {Hs : Ok s},
     In y (add x s) <-> X.eq y x \/ In y s.
  Proof.
  induction s; simpl; intros.
  intuition; inv; auto.
  destruct X.eq_dec; inv; rewrite InA_cons, ?IHs; intuition.
  left; eauto.
  inv; auto.
  Qed.

  Global Instance add_ok s x `(Ok s) : Ok (add x s).
  Proof.
  induction s.
  simpl; intuition.
  intros; inv. simpl.
  destruct X.eq_dec; auto.
  constructors; auto.
  intro; inv; auto.
  rewrite add_spec in *; intuition.
  Qed.

  Lemma remove_spec :
   forall (s : t) (x y : elt) {Hs : Ok s},
     In y (remove x s) <-> In y s /\ ~X.eq y x.
  Proof.
  induction s; simpl; intros.
  intuition; inv; auto.
  destruct X.eq_dec as [|Hnot]; inv; rewrite !InA_cons, ?IHs; intuition.
  elim H. setoid_replace a with y; eauto.
  elim H3. setoid_replace x with y; eauto.
  elim Hnot. eauto.
  Qed.

  Global Instance remove_ok s x `(Ok s) : Ok (remove x s).
  Proof.
  induction s; simpl; intros.
  auto.
  destruct X.eq_dec; inv; auto.
  constructors; auto.
  rewrite remove_spec; intuition.
  Qed.

  Lemma singleton_ok : forall x : elt, Ok (singleton x).
  Proof.
  unfold singleton; simpl; constructors; auto. intro; inv.
  Qed.

  Lemma singleton_spec : forall x y : elt, In y (singleton x) <-> X.eq y x.
  Proof.
  unfold singleton; simpl; split; intros. inv; auto. left; auto.
  Qed.

  Lemma empty_ok : Ok empty.
  Proof.
  unfold empty; constructors.
  Qed.

  Lemma empty_spec : Empty empty.
  Proof.
  unfold Empty, empty; red; intros; inv.
  Qed.

  Lemma is_empty_spec : forall s : t, is_empty s = true <-> Empty s.
  Proof.
  unfold Empty; destruct s; simpl; split; intros; auto.
  intro; inv.
  discriminate.
  elim (H e); auto.
  Qed.

  Lemma elements_spec1 : forall (s : t) (x : elt), In x (elements s) <-> In x s.
  Proof.
  unfold elements; intuition.
  Qed.

  Lemma elements_spec2w : forall (s : t) {Hs : Ok s}, NoDup (elements s).
  Proof.
  unfold elements; auto.
  Qed.

  Lemma fold_spec :
   forall (s : t) (A : Type) (i : A) (f : elt -> A -> A),
   fold f s i = fold_left (flip f) (elements s) i.
  Proof.
  reflexivity.
  Qed.

  Global Instance union_ok : forall s s' `(Ok s, Ok s'), Ok (union s s').
  Proof.
  induction s; simpl; auto; intros; inv; unfold flip; auto with *.
  Qed.

  Lemma union_spec :
   forall (s s' : t) (x : elt) {Hs : Ok s} {Hs' : Ok s'},
   In x (union s s') <-> In x s \/ In x s'.
  Proof.
  induction s; simpl in *; unfold flip; intros; auto; inv.
  intuition; inv.
  rewrite IHs, add_spec, InA_cons; intuition.
  Qed.

  Global Instance inter_ok s s' `(Ok s, Ok s') : Ok (inter s s').
  Proof.
  unfold inter, fold, flip.
  set (acc := nil (A:=elt)).
  assert (Hacc : Ok acc) by constructors.
  clearbody acc; revert acc Hacc.
  induction s; simpl; auto; intros. inv.
  apply IHs; auto.
  destruct (mem a s'); auto with *.
  Qed.

  Lemma inter_spec  :
   forall (s s' : t) (x : elt) {Hs : Ok s} {Hs' : Ok s'},
   In x (inter s s') <-> In x s /\ In x s'.
  Proof.
  unfold inter, fold, flip; intros.
  set (acc := nil (A:=elt)) in *.
  assert (Hacc : Ok acc) by constructors.
  assert (IFF : (In x s /\ In x s') <-> (In x s /\ In x s') \/ In x acc).
   intuition; unfold acc in *; inv.
  rewrite IFF; clear IFF. clearbody acc.
  revert acc Hacc x s' Hs Hs'.
  induction s; simpl; intros.
  intuition; inv.
  inv.
  case_eq (mem a s'); intros Hm.
  rewrite IHs, add_spec, InA_cons; intuition.
  rewrite mem_spec in Hm; auto.
  left; split; auto. rewrite H1; auto.
  rewrite IHs, InA_cons; intuition.
  rewrite H2, <- mem_spec in H3; auto. congruence.
  Qed.

  Global Instance diff_ok : forall s s' `(Ok s, Ok s'), Ok (diff s s').
  Proof.
  unfold diff; intros s s'; revert s.
  induction s'; simpl; unfold flip; auto; intros. inv; auto with *.
  Qed.

  Lemma diff_spec  :
   forall (s s' : t) (x : elt) {Hs : Ok s} {Hs' : Ok s'},
   In x (diff s s') <-> In x s /\ ~In x s'.
  Proof.
  unfold diff; intros s s'; revert s.
  induction s'; simpl; unfold flip.
  intuition; inv.
  intros. inv.
  rewrite IHs', remove_spec, InA_cons; intuition.
  Qed.

  Lemma subset_spec :
   forall (s s' : t) {Hs : Ok s} {Hs' : Ok s'},
   subset s s' = true <-> Subset s s'.
  Proof.
  unfold subset, Subset; intros.
  rewrite is_empty_spec.
  unfold Empty; intros.
  intuition.
  specialize (H a). rewrite diff_spec in H; intuition.
  rewrite <- (mem_spec a) in H |- *. destruct (mem a s'); intuition.
  rewrite diff_spec in H0; intuition.
  Qed.

  Lemma equal_spec :
   forall (s s' : t) {Hs : Ok s} {Hs' : Ok s'},
   equal s s' = true <-> Equal s s'.
  Proof.
  unfold Equal, equal; intros.
  rewrite andb_true_iff, !subset_spec.
  unfold Subset; intuition. rewrite <- H; auto. rewrite H; auto.
  Qed.

  Definition choose_spec1 :
    forall (s : t) (x : elt), choose s = Some x -> In x s.
  Proof.
  destruct s; simpl; intros; inversion H; auto.
  Qed.

  Definition choose_spec2 : forall s : t, choose s = None -> Empty s.
  Proof.
  destruct s; simpl; intros.
  intros x H0; inversion H0.
  inversion H.
  Qed.

  Lemma cardinal_spec :
   forall (s : t) {Hs : Ok s}, cardinal s = length (elements s).
  Proof.
  auto.
  Qed.

  Lemma filter_spec' : forall s x f,
   In x (filter f s) -> In x s.
  Proof.
  induction s; simpl.
  intuition; inv.
  intros; destruct (f a); inv; intuition; right; eauto.
  Qed.

  Lemma filter_spec :
   forall (s : t) (x : elt) (f : elt -> bool),
   Proper (X.eq==>eq) f ->
   (In x (filter f s) <-> In x s /\ f x = true).
  Proof.
  induction s; simpl.
  intuition; inv.
  intros.
  destruct (f a) eqn:E; rewrite ?InA_cons, IHs; intuition.
  setoid_replace x with a; auto.
  setoid_replace a with x in E; auto. congruence.
  Qed.

  Global Instance filter_ok s f `(Ok s) : Ok (filter f s).
  Proof.
  induction s; simpl.
  auto.
  intros; inv.
  case (f a); auto.
  constructors; auto.
  contradict H0.
  eapply filter_spec'; eauto.
  Qed.

  Lemma for_all_spec :
   forall (s : t) (f : elt -> bool),
   Proper (X.eq==>eq) f ->
   (for_all f s = true <-> For_all (fun x => f x = true) s).
  Proof.
  unfold For_all; induction s; simpl.
  intuition. inv.
  intros; inv.
  destruct (f a) eqn:F.
  rewrite IHs; intuition. inv; auto.
  setoid_replace x with a; auto.
  split; intros H'; try discriminate.
  intros.
  rewrite <- F, <- (H' a); auto.
  Qed.

  Lemma exists_spec :
   forall (s : t) (f : elt -> bool),
   Proper (X.eq==>eq) f ->
   (exists_ f s = true <-> Exists (fun x => f x = true) s).
  Proof.
  unfold Exists; induction s; simpl.
  split; [discriminate| intros (x & Hx & _); inv].
  intros.
  destruct (f a) eqn:F.
  split; auto.
  exists a; auto.
  rewrite IHs; firstorder.
  inv.
  setoid_replace a with x in F; auto; congruence.
  exists x; auto.
  Qed.

  Lemma partition_spec1 :
   forall (s : t) (f : elt -> bool),
   Proper (X.eq==>eq) f ->
   Equal (fst (partition f s)) (filter f s).
  Proof.
  simple induction s; simpl; auto; unfold Equal.
  firstorder.
  intros x l Hrec f Hf.
  generalize (Hrec f Hf); clear Hrec.
  case (partition f l); intros s1 s2; simpl; intros.
  case (f x); simpl; firstorder; inversion H0; intros; firstorder.
  Qed.

  Lemma partition_spec2 :
   forall (s : t) (f : elt -> bool),
   Proper (X.eq==>eq) f ->
   Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
  Proof.
  simple induction s; simpl; auto; unfold Equal.
  firstorder.
  intros x l Hrec f Hf.
  generalize (Hrec f Hf); clear Hrec.
  case (partition f l); intros s1 s2; simpl; intros.
  case (f x); simpl; firstorder; inversion H0; intros; firstorder.
  Qed.

  Lemma partition_ok1' :
   forall (s : t) {Hs : Ok s} (f : elt -> bool)(x:elt),
    In x (fst (partition f s)) -> In x s.
  Proof.
  induction s; simpl; auto; intros. inv.
  generalize (IHs H1 f x).
  destruct (f a); destruct (partition f s); simpl in *; auto.
  inversion_clear H; auto.
  Qed.

  Lemma partition_ok2' :
   forall (s : t) {Hs : Ok s} (f : elt -> bool)(x:elt),
    In x (snd (partition f s)) -> In x s.
  Proof.
  induction s; simpl; auto; intros. inv.
  generalize (IHs H1 f x).
  destruct (f a); destruct (partition f s); simpl in *; auto.
  inversion_clear H; auto.
  Qed.

  Global Instance partition_ok1 : forall s f `(Ok s), Ok (fst (partition f s)).
  Proof.
  simple induction s; simpl.
  auto.
  intros x l Hrec f Hs; inv.
  generalize (@partition_ok1' _ _ f x).
  generalize (Hrec f H0).
  case (f x); case (partition f l); simpl; constructors; auto.
  Qed.

  Global Instance partition_ok2 : forall s f `(Ok s), Ok (snd (partition f s)).
  Proof.
  simple induction s; simpl.
  auto.
  intros x l Hrec f Hs; inv.
  generalize (@partition_ok2' _ _ f x).
  generalize (Hrec f H0).
  case (f x); case (partition f l); simpl; constructors; auto.
  Qed.

  End ForNotations.

  Definition In := InA X.eq.
  Definition eq := Equal.
  Instance eq_equiv : Equivalence eq := _.

End MakeRaw.

(** * Encapsulation

   Now, in order to really provide a functor implementing [S], we
   need to encapsulate everything into a type of lists without redundancy. *)

Module Make (X: DecidableType) <: WSets with Module E := X.
 Module Raw := MakeRaw X.
 Include WRaw2Sets X Raw.
End Make.


(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** A library for finite sets, implemented as lists *)

(** This is a light implementation of finite sets as lists; for a more
    extensive library, you might rather consider MSetWeakList.v. In
    addition, if your domain is totally ordered, you might also
    consider implementations of finite sets with access in logarithmic
    time (e.g. MSetRBT.v which is based on red-black trees). *)

Require Import List.

Set Implicit Arguments.

Section first_definitions.

  Variable A : Type.
  Hypothesis Aeq_dec : forall x y:A, {x = y} + {x <> y}.

  Definition set := list A.

  Definition empty_set : set := nil.

  Fixpoint set_add (a:A) (x:set) : set :=
    match x with
    | nil => a :: nil
    | a1 :: x1 =>
        match Aeq_dec a a1 with
        | left _ => a1 :: x1
        | right _ => a1 :: set_add a x1
        end
    end.


  Fixpoint set_mem (a:A) (x:set) : bool :=
    match x with
    | nil => false
    | a1 :: x1 =>
        match Aeq_dec a a1 with
        | left _ => true
        | right _ => set_mem a x1
        end
    end.

  (** If [a] belongs to [x], removes [a] from [x]. If not, does nothing.
      Invariant: any element should occur at most once in [x], see for
      instance [set_add]. We hence remove here only the first occurrence
      of [a] in [x]. *)

  Fixpoint set_remove (a:A) (x:set) : set :=
    match x with
    | nil => empty_set
    | a1 :: x1 =>
        match Aeq_dec a a1 with
        | left _ => x1
        | right _ => a1 :: set_remove a x1
        end
    end.

  Fixpoint set_inter (x:set) : set -> set :=
    match x with
    | nil => fun y => nil
    | a1 :: x1 =>
        fun y =>
          if set_mem a1 y then a1 :: set_inter x1 y else set_inter x1 y
    end.

  Fixpoint set_union (x y:set) : set :=
    match y with
    | nil => x
    | a1 :: y1 => set_add a1 (set_union x y1)
    end.

  (** returns the set of all els of [x] that does not belong to [y] *)
  Fixpoint set_diff (x y:set) : set :=
    match x with
    | nil => nil
    | a1 :: x1 =>
        if set_mem a1 y then set_diff x1 y else set_add a1 (set_diff x1 y)
    end.


  Definition set_In : A -> set -> Prop := In (A:=A).

  Lemma set_In_dec : forall (a:A) (x:set), {set_In a x} + {~ set_In a x}.

  Proof.
    unfold set_In.
    (*** Realizer set_mem. Program_all. ***)
    simple induction x.
    auto.
    intros a0 x0 Ha0. case (Aeq_dec a a0); intro eq.
    rewrite eq; simpl; auto with datatypes.
    elim Ha0.
    auto with datatypes.
    right; simpl; unfold not; intros [Hc1| Hc2];
     auto with datatypes.
  Qed.

  Lemma set_mem_ind :
   forall (B:Type) (P:B -> Prop) (y z:B) (a:A) (x:set),
     (set_In a x -> P y) -> P z -> P (if set_mem a x then y else z).

  Proof.
    simple induction x; simpl; intros.
    assumption.
    elim (Aeq_dec a a0); auto with datatypes.
  Qed.

  Lemma set_mem_ind2 :
   forall (B:Type) (P:B -> Prop) (y z:B) (a:A) (x:set),
     (set_In a x -> P y) ->
     (~ set_In a x -> P z) -> P (if set_mem a x then y else z).

  Proof.
    simple induction x; simpl; intros.
    apply H0; red; trivial.
    case (Aeq_dec a a0); auto with datatypes.
    intro Hneg; apply H; intros; auto.
    apply H1; red; intro.
    case H3; auto.
  Qed.


  Lemma set_mem_correct1 :
   forall (a:A) (x:set), set_mem a x = true -> set_In a x.
  Proof.
    simple induction x; simpl.
    discriminate.
    intros a0 l; elim (Aeq_dec a a0); auto with datatypes.
  Qed.

  Lemma set_mem_correct2 :
   forall (a:A) (x:set), set_In a x -> set_mem a x = true.
  Proof.
    simple induction x; simpl.
    intro Ha; elim Ha.
    intros a0 l; elim (Aeq_dec a a0); auto with datatypes.
    intros H1 H2 [H3| H4].
    absurd (a0 = a); auto with datatypes.
    auto with datatypes.
  Qed.

  Lemma set_mem_complete1 :
   forall (a:A) (x:set), set_mem a x = false -> ~ set_In a x.
  Proof.
    simple induction x; simpl.
    tauto.
    intros a0 l; elim (Aeq_dec a a0).
    intros _ _ [=].
    unfold not; intros H H0 H1 [|]; auto with datatypes.
  Qed.

  Lemma set_mem_complete2 :
   forall (a:A) (x:set), ~ set_In a x -> set_mem a x = false.
  Proof.
    simple induction x; simpl.
    tauto.
    intros a0 l; elim (Aeq_dec a a0).
    intros H H0 []; auto with datatypes.
    tauto.
  Qed.

  Lemma set_add_intro1 :
   forall (a b:A) (x:set), set_In a x -> set_In a (set_add b x).

  Proof.
    unfold set_In; simple induction x; simpl.
    auto with datatypes.
    intros a0 l H [Ha0a| Hal].
    elim (Aeq_dec b a0); left; assumption.
    elim (Aeq_dec b a0); right; [ assumption | auto with datatypes ].
  Qed.

  Lemma set_add_intro2 :
   forall (a b:A) (x:set), a = b -> set_In a (set_add b x).

  Proof.
    unfold set_In; simple induction x; simpl.
    auto with datatypes.
    intros a0 l H Hab.
    elim (Aeq_dec b a0);
     [ rewrite Hab; intro Hba0; rewrite Hba0; simpl;
        auto with datatypes
     | auto with datatypes ].
  Qed.

  Hint Resolve set_add_intro1 set_add_intro2.

  Lemma set_add_intro :
   forall (a b:A) (x:set), a = b \/ set_In a x -> set_In a (set_add b x).

  Proof.
    intros a b x [H1| H2]; auto with datatypes.
  Qed.

  Lemma set_add_elim :
   forall (a b:A) (x:set), set_In a (set_add b x) -> a = b \/ set_In a x.

  Proof.
    unfold set_In.
    simple induction x.
    simpl; intros [H1| H2]; auto with datatypes.
    simpl; do 3 intro.
    elim (Aeq_dec b a0).
    simpl; tauto.
    simpl; intros H0 [|].
    trivial with datatypes.
    tauto.
    tauto.
  Qed.

  Lemma set_add_elim2 :
   forall (a b:A) (x:set), set_In a (set_add b x) -> a <> b -> set_In a x.
   intros a b x H; case (set_add_elim _ _ _ H); intros; trivial.
   case H1; trivial.
   Qed.

  Hint Resolve set_add_intro set_add_elim set_add_elim2.

  Lemma set_add_not_empty : forall (a:A) (x:set), set_add a x <> empty_set.
  Proof.
    simple induction x; simpl.
    discriminate.
    intros; elim (Aeq_dec a a0); intros; discriminate.
  Qed.

  Lemma set_add_iff a b l : In a (set_add b l) <-> a = b \/ In a l.
  Proof.
  split. apply set_add_elim. apply set_add_intro.
  Qed.

  Lemma set_add_nodup a l : NoDup l -> NoDup (set_add a l).
  Proof.
   induction 1 as [|x l H H' IH]; simpl.
   - constructor; [ tauto | constructor ].
   - destruct (Aeq_dec a x) as [<-|Hax]; constructor; trivial.
     rewrite set_add_iff. intuition.
  Qed.

  Lemma set_remove_1 (a b : A) (l : set) :
    In a (set_remove b l) -> In a l.
  Proof.
    induction l as [|x xs Hrec].
    - intros. auto.
    - simpl. destruct (Aeq_dec b x).
      * tauto.
      * intro H. destruct H.
        + rewrite H. apply in_eq.
      + apply in_cons. apply Hrec. assumption.
  Qed.

  Lemma set_remove_2 (a b:A) (l : set) :
    NoDup l -> In a (set_remove b l) -> a <> b.
  Proof.
    induction l as [|x l IH]; intro ND; simpl.
    - tauto.
    - inversion_clear ND.
      destruct (Aeq_dec b x) as [<-|Hbx].
      + congruence.
      + destruct 1; subst; auto.
  Qed.

  Lemma set_remove_3 (a b : A) (l : set) :
    In a l -> a <> b -> In a (set_remove b l).
  Proof.
    induction l as [|x xs Hrec].
    - now simpl.
    - simpl. destruct (Aeq_dec b x) as [<-|Hbx]; simpl; intuition.
      congruence.
  Qed.

  Lemma set_remove_iff (a b : A) (l : set) :
   NoDup l -> (In a (set_remove b l) <-> In a l /\ a <> b).
  Proof.
   split; try split.
   - eapply set_remove_1; eauto.
   - eapply set_remove_2; eauto.
   - destruct 1; apply set_remove_3; auto.
  Qed.

  Lemma set_remove_nodup a l : NoDup l -> NoDup (set_remove a l).
  Proof.
   induction 1 as [|x l H H' IH]; simpl.
   - constructor.
   - destruct (Aeq_dec a x) as [<-|Hax]; trivial.
     constructor; trivial.
     rewrite set_remove_iff; trivial. intuition.
  Qed.

  Lemma set_union_intro1 :
   forall (a:A) (x y:set), set_In a x -> set_In a (set_union x y).
  Proof.
    simple induction y; simpl; auto with datatypes.
  Qed.

  Lemma set_union_intro2 :
   forall (a:A) (x y:set), set_In a y -> set_In a (set_union x y).
  Proof.
    simple induction y; simpl.
    tauto.
    intros; elim H0; auto with datatypes.
  Qed.

  Hint Resolve set_union_intro2 set_union_intro1.

  Lemma set_union_intro :
   forall (a:A) (x y:set),
     set_In a x \/ set_In a y -> set_In a (set_union x y).
  Proof.
    intros; elim H; auto with datatypes.
  Qed.

  Lemma set_union_elim :
   forall (a:A) (x y:set),
     set_In a (set_union x y) -> set_In a x \/ set_In a y.
  Proof.
    simple induction y; simpl.
    auto with datatypes.
    intros.
    generalize (set_add_elim _ _ _ H0).
    intros [H1| H1].
    auto with datatypes.
    tauto.
  Qed.

  Lemma set_union_iff a l l': In a (set_union l l') <-> In a l \/ In a l'.
  Proof.
    split. apply set_union_elim. apply set_union_intro.
  Qed.

  Lemma set_union_nodup l l' : NoDup l -> NoDup l' -> NoDup (set_union l l').
  Proof.
   induction 2 as [|x' l' ? ? IH]; simpl; trivial. now apply set_add_nodup.
  Qed.

  Lemma set_union_emptyL :
   forall (a:A) (x:set), set_In a (set_union empty_set x) -> set_In a x.
    intros a x H; case (set_union_elim _ _ _ H); auto || contradiction.
  Qed.

  Lemma set_union_emptyR :
   forall (a:A) (x:set), set_In a (set_union x empty_set) -> set_In a x.
    intros a x H; case (set_union_elim _ _ _ H); auto || contradiction.
  Qed.

  Lemma set_inter_intro :
   forall (a:A) (x y:set),
     set_In a x -> set_In a y -> set_In a (set_inter x y).
  Proof.
    simple induction x.
    auto with datatypes.
    simpl; intros a0 l Hrec y [Ha0a| Hal] Hy.
    simpl; rewrite Ha0a.
    generalize (set_mem_correct1 a y).
    generalize (set_mem_complete1 a y).
    elim (set_mem a y); simpl; intros.
    auto with datatypes.
    absurd (set_In a y); auto with datatypes.
    elim (set_mem a0 y); [ right; auto with datatypes | auto with datatypes ].
  Qed.

  Lemma set_inter_elim1 :
   forall (a:A) (x y:set), set_In a (set_inter x y) -> set_In a x.
  Proof.
    simple induction x.
    auto with datatypes.
    simpl; intros a0 l Hrec y.
    generalize (set_mem_correct1 a0 y).
    elim (set_mem a0 y); simpl; intros.
    elim H0; eauto with datatypes.
    eauto with datatypes.
  Qed.

  Lemma set_inter_elim2 :
   forall (a:A) (x y:set), set_In a (set_inter x y) -> set_In a y.
  Proof.
    simple induction x.
    simpl; tauto.
    simpl; intros a0 l Hrec y.
    generalize (set_mem_correct1 a0 y).
    elim (set_mem a0 y); simpl; intros.
    elim H0;
     [ intro Hr; rewrite <- Hr; eauto with datatypes | eauto with datatypes ].
    eauto with datatypes.
  Qed.

  Hint Resolve set_inter_elim1 set_inter_elim2.

  Lemma set_inter_elim :
   forall (a:A) (x y:set),
     set_In a (set_inter x y) -> set_In a x /\ set_In a y.
  Proof.
    eauto with datatypes.
  Qed.

  Lemma set_inter_iff a l l' : In a (set_inter l l') <-> In a l /\ In a l'.
  Proof.
    split.
    - apply set_inter_elim.
    - destruct 1. now apply set_inter_intro.
  Qed.

  Lemma set_inter_nodup l l' : NoDup l -> NoDup l' -> NoDup (set_inter l l').
  Proof.
   induction 1 as [|x l H H' IH]; intro Hl'; simpl.
   - constructor.
   - destruct (set_mem x l'); auto.
     constructor; auto. rewrite set_inter_iff; tauto.
  Qed.

  Lemma set_diff_intro :
   forall (a:A) (x y:set),
     set_In a x -> ~ set_In a y -> set_In a (set_diff x y).
  Proof.
    simple induction x.
    simpl; tauto.
    simpl; intros a0 l Hrec y [Ha0a| Hal] Hay.
    rewrite Ha0a; generalize (set_mem_complete2 _ _ Hay).
    elim (set_mem a y);
     [ intro Habs; discriminate Habs | auto with datatypes ].
    elim (set_mem a0 y); auto with datatypes.
  Qed.

  Lemma set_diff_elim1 :
   forall (a:A) (x y:set), set_In a (set_diff x y) -> set_In a x.
  Proof.
    simple induction x.
    simpl; tauto.
    simpl; intros a0 l Hrec y; elim (set_mem a0 y).
    eauto with datatypes.
    intro; generalize (set_add_elim _ _ _ H).
    intros [H1| H2]; eauto with datatypes.
  Qed.

  Lemma set_diff_elim2 :
   forall (a:A) (x y:set), set_In a (set_diff x y) -> ~ set_In a y.
  intros a x y; elim x; simpl.
  intros; contradiction.
  intros a0 l Hrec.
  apply set_mem_ind2; auto.
  intros H1 H2; case (set_add_elim _ _ _ H2); intros; auto.
  rewrite H; trivial.
  Qed.

  Lemma set_diff_iff a l l' : In a (set_diff l l') <-> In a l /\ ~In a l'.
  Proof.
  split.
  - split; [eapply set_diff_elim1 | eapply set_diff_elim2]; eauto.
  - destruct 1. now apply set_diff_intro.
  Qed.

  Lemma set_diff_nodup l l' : NoDup l -> NoDup l' -> NoDup (set_diff l l').
  Proof.
   induction 1 as [|x l H H' IH]; intro Hl'; simpl.
   - constructor.
   - destruct (set_mem x l'); auto using set_add_nodup.
  Qed.

  Lemma set_diff_trivial : forall (a:A) (x:set), ~ set_In a (set_diff x x).
  red; intros a x H.
  apply (set_diff_elim2 _ _ _ H).
  apply (set_diff_elim1 _ _ _ H).
  Qed.

Hint Resolve set_diff_intro set_diff_trivial.


End first_definitions.

Section other_definitions.

  Definition set_prod : forall {A B:Type}, set A -> set B -> set (A * B) :=
    list_prod.

  (** [B^A], set of applications from [A] to [B] *)
  Definition set_power : forall {A B:Type}, set A -> set B -> set (set (A * B)) :=
    list_power.

  Definition set_fold_left {A B:Type} : (B -> A -> B) -> set A -> B -> B :=
    fold_left (A:=B) (B:=A).

  Definition set_fold_right {A B:Type} (f:A -> B -> B) (x:set A)
    (b:B) : B := fold_right f b x.

  Definition set_map {A B:Type} (Aeq_dec : forall x y:B, {x = y} + {x <> y})
    (f : A -> B) (x : set A) : set B :=
    set_fold_right (fun a => set_add Aeq_dec (f a)) x (empty_set B).

End other_definitions.

Unset Implicit Arguments.

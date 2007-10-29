(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(** * Finite sets library *)

(** This file proposes an implementation of the non-dependant 
    interface [FSetWeakInterface.S] using lists without redundancy. *)

Require Import FSetWeakInterface.
Set Implicit Arguments.
Unset Strict Implicit.

(** * Functions over lists

   First, we provide sets as lists which are (morally) without redundancy.
   The specs are proved under the additional condition of no redundancy. 
   And the functions returning sets are proved to preserve this invariant. *)

Module Raw (X: DecidableType).
 
  Module E := X.

  Definition elt := X.t.
  Definition t := list elt.

  Definition empty : t := nil.

  Definition is_empty (l : t) : bool := if l then true else false.

  (** ** The set operations. *)

  Fixpoint mem (x : elt) (s : t) {struct s} : bool :=
    match s with
    | nil => false
    | y :: l =>
           if X.eq_dec x y then true else mem x l
    end.

  Fixpoint add (x : elt) (s : t) {struct s} : t :=
    match s with
    | nil => x :: nil
    | y :: l =>
        if X.eq_dec x y then s else y :: add x l
    end.

  Definition singleton (x : elt) : t := x :: nil. 

  Fixpoint remove (x : elt) (s : t) {struct s} : t :=
    match s with
    | nil => nil
    | y :: l =>
        if X.eq_dec x y then l else y :: remove x l
    end.

  Fixpoint fold (B : Type) (f : elt -> B -> B) (s : t) {struct s} : 
   B -> B := fun i => match s with
                      | nil => i
                      | x :: l => fold f l (f x i)
                      end.  

  Definition union (s : t) : t -> t := fold add s.
  
  Definition diff (s s' : t) : t := fold remove s' s.

  Definition inter (s s': t) : t := 
    fold (fun x s => if mem x s' then add x s else s) s nil.

  Definition subset (s s' : t) : bool := is_empty (diff s s').

  Definition equal (s s' : t) : bool := andb (subset s s') (subset s' s). 

  Fixpoint filter (f : elt -> bool) (s : t) {struct s} : t :=
    match s with
    | nil => nil
    | x :: l => if f x then x :: filter f l else filter f l
    end.  

  Fixpoint for_all (f : elt -> bool) (s : t) {struct s} : bool :=
    match s with
    | nil => true
    | x :: l => if f x then for_all f l else false
    end.  
 
  Fixpoint exists_ (f : elt -> bool) (s : t) {struct s} : bool :=
    match s with
    | nil => false
    | x :: l => if f x then true else exists_ f l
    end.

  Fixpoint partition (f : elt -> bool) (s : t) {struct s} : 
   t * t :=
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

  (** ** Proofs of set operation specifications. *)
  Section ForNotations. 
  Notation NoDup := (NoDupA X.eq).
  Notation In := (InA X.eq).

  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.

  Lemma In_eq :
    forall (s : t) (x y : elt), X.eq x y -> In x s -> In y s.
  Proof.
  intros s x y; do 2 setoid_rewrite InA_alt; firstorder eauto.
  Qed.
  Hint Immediate In_eq.

  Lemma mem_1 :
   forall (s : t)(x : elt), In x s -> mem x s = true. 
  Proof.
  induction s; intros.
  inversion H.
  simpl; destruct (X.eq_dec x a); trivial.
  inversion_clear H; auto.
  Qed.

  Lemma mem_2 : forall (s : t) (x : elt), mem x s = true -> In x s.
  Proof.
  induction s. 
  intros; inversion H.
  intros x; simpl.
  destruct (X.eq_dec x a); firstorder; discriminate.
  Qed.

  Lemma add_1 :
   forall (s : t) (Hs : NoDup s) (x y : elt), X.eq x y -> In y (add x s).
  Proof.
  induction s. 
  simpl; intuition.
  simpl; intros; case (X.eq_dec x a); intuition; inversion_clear Hs;
   firstorder.
  eauto.
  Qed.

  Lemma add_2 :
   forall (s : t) (Hs : NoDup s) (x y : elt), In y s -> In y (add x s).
  Proof.
  induction s. 
  simpl; intuition.
  simpl; intros; case (X.eq_dec x a); intuition.
  inversion_clear Hs; eauto; inversion_clear H; intuition.
  Qed.

  Lemma add_3 :
   forall (s : t) (Hs : NoDup s) (x y : elt),
   ~ X.eq x y -> In y (add x s) -> In y s.
  Proof.
  induction s. 
  simpl; intuition.
  inversion_clear H0; firstorder; absurd (X.eq x y); auto.
  simpl; intros Hs x y; case (X.eq_dec x a); intros;
   inversion_clear H0; inversion_clear Hs; firstorder; 
   absurd (X.eq x y); auto.
  Qed.

  Lemma add_unique :
   forall (s : t) (Hs : NoDup s)(x:elt), NoDup (add x s).
  Proof.
  induction s.  
  simpl; intuition.
  constructor; auto.
  intro H0; inversion H0.
  intros.
  inversion_clear Hs.
  simpl.
  destruct (X.eq_dec x a).
  constructor; auto.
  constructor; auto.
  intro H1; apply H.
  eapply add_3; eauto.
  Qed.

  Lemma remove_1 :
   forall (s : t) (Hs : NoDup s) (x y : elt), X.eq x y -> ~ In y (remove x s).
  Proof.
  simple induction s. 
  simpl; red; intros; inversion H0.
  simpl; intros; case (X.eq_dec x a); intuition; inversion_clear Hs. 
  elim H2.
  apply In_eq with y; eauto.
  inversion_clear H1; eauto.
  Qed.

  Lemma remove_2 :
   forall (s : t) (Hs : NoDup s) (x y : elt),
   ~ X.eq x y -> In y s -> In y (remove x s).
  Proof.
  simple induction s. 
  simpl; intuition.
  simpl; intros; case (X.eq_dec x a); intuition; inversion_clear Hs;
   inversion_clear H1; auto. 
  absurd (X.eq x y); eauto. 
  Qed.

  Lemma remove_3 :
   forall (s : t) (Hs : NoDup s) (x y : elt), In y (remove x s) -> In y s.
  Proof.
  simple induction s. 
  simpl; intuition.
  simpl; intros a l Hrec Hs x y; case (X.eq_dec x a); intuition.
  inversion_clear Hs; inversion_clear H; firstorder.
  Qed.

  Lemma remove_unique :
   forall (s : t) (Hs : NoDup s) (x : elt), NoDup (remove x s).
  Proof.
  simple induction s.
  simpl; intuition.
  simpl; intros; case (X.eq_dec x a); intuition; inversion_clear Hs;
   auto.
  constructor; auto.
  intro H2; elim H0.
  eapply remove_3; eauto.
  Qed. 

  Lemma singleton_unique : forall x : elt, NoDup (singleton x).
  Proof.
  unfold singleton; simpl; constructor; auto; intro H; inversion H.
  Qed.

  Lemma singleton_1 : forall x y : elt, In y (singleton x) -> X.eq x y.
  Proof.
  unfold singleton; simpl; intuition.
  inversion_clear H; auto; inversion H0.
  Qed. 

  Lemma singleton_2 : forall x y : elt, X.eq x y -> In y (singleton x).
  Proof.
  unfold singleton; simpl; intuition.
  Qed. 
  
  Lemma empty_unique : NoDup empty.
  Proof.
  unfold empty; constructor.
  Qed.

  Lemma empty_1 : Empty empty.
  Proof.
  unfold Empty, empty; intuition; inversion H.
  Qed. 

  Lemma is_empty_1 : forall s : t, Empty s -> is_empty s = true.
  Proof.
  unfold Empty; intro s; case s; simpl; intuition.
  elim (H e); auto.
  Qed.
  
  Lemma is_empty_2 : forall s : t, is_empty s = true -> Empty s. 
  Proof.
  unfold Empty; intro s; case s; simpl; intuition;
   inversion H0.
  Qed.

  Lemma elements_1 : forall (s : t) (x : elt), In x s -> In x (elements s).
  Proof.
  unfold elements; auto.
  Qed.

  Lemma elements_2 : forall (s : t) (x : elt), In x (elements s) -> In x s.
  Proof. 
  unfold elements; auto.
  Qed.
 
  Lemma elements_3w : forall (s : t) (Hs : NoDup s), NoDup (elements s).  
  Proof. 
  unfold elements; auto.
  Qed.

  Lemma fold_1 :
   forall (s : t) (Hs : NoDup s) (A : Type) (i : A) (f : elt -> A -> A),
   fold f s i = fold_left (fun a e => f e a) (elements s) i.
  Proof.
  induction s; simpl; auto; intros.
  inversion_clear Hs; auto.
  Qed.

  Lemma union_unique :
   forall (s s' : t) (Hs : NoDup s) (Hs' : NoDup s'), NoDup (union s s').
  Proof.
  unfold union; induction s; simpl; auto; intros.
  inversion_clear Hs.
  apply IHs; auto.
  apply add_unique; auto.
  Qed.
  
  Lemma union_1 :
   forall (s s' : t) (Hs : NoDup s) (Hs' : NoDup s') (x : elt),
   In x (union s s') -> In x s \/ In x s'.
  Proof.
  unfold union; induction s; simpl; auto; intros.
  inversion_clear Hs.
  destruct (X.eq_dec x a).
  left; auto.
  destruct (IHs (add a s') H1 (add_unique Hs' a) x); intuition.
  right; eapply add_3; eauto.
  Qed.

  Lemma union_0 : 
   forall (s s' : t) (Hs : NoDup s) (Hs' : NoDup s') (x : elt),
   In x s \/ In x s' -> In x (union s s').
  Proof.
  unfold union; induction s; simpl; auto; intros.
  inversion_clear H; auto.
  inversion_clear H0.
  inversion_clear Hs.
  apply IHs; auto.
  apply add_unique; auto.
  destruct H.
  inversion_clear H; auto.
  right; apply add_1; auto.
  right; apply add_2; auto.
  Qed.

  Lemma union_2 :
   forall (s s' : t) (Hs : NoDup s) (Hs' : NoDup s') (x : elt),
   In x s -> In x (union s s').
  Proof.
  intros; apply union_0; auto.
  Qed.

  Lemma union_3 :
   forall (s s' : t) (Hs : NoDup s) (Hs' : NoDup s') (x : elt),
   In x s' -> In x (union s s').
  Proof.
  intros; apply union_0; auto.
  Qed.

  Lemma inter_unique :
   forall (s s' : t) (Hs : NoDup s) (Hs' : NoDup s'), NoDup (inter s s').
  Proof.
  unfold inter; intros s.
  set (acc := nil (A:=elt)).
  assert (NoDup acc) by (unfold acc; auto).
  clearbody acc; generalize H; clear H; generalize acc; clear acc. 
  induction s; simpl; auto; intros.
  inversion_clear Hs.
  apply IHs; auto.
  destruct (mem a s'); intros; auto.
  apply add_unique; auto.
  Qed.  
  
  Lemma inter_0  :
   forall (s s' : t) (Hs : NoDup s) (Hs' : NoDup s') (x : elt),
   In x (inter s s') -> In x s /\ In x s'.
  Proof.
  unfold inter; intros.
  set (acc := nil (A:=elt)) in *.
  assert (NoDup acc) by (unfold acc; auto).
  cut ((In x s /\ In x s') \/ In x acc).
    destruct 1; auto.
    inversion H1.
  clearbody acc. 
  generalize H0 H Hs' Hs; clear H0 H Hs Hs'.
  generalize acc x s'; clear acc x s'.
  induction s; simpl; auto; intros.
  inversion_clear Hs.
  case_eq (mem a s'); intros H3; rewrite H3 in H; simpl in H.
  destruct (IHs _ _ _ (add_unique H0 a) H); auto.
  left; intuition.
  destruct (X.eq_dec x a); auto.
  left; intuition.
  apply In_eq with a; eauto.
  apply mem_2; auto.
  right; eapply add_3; eauto.
  destruct (IHs _ _ _ H0 H); auto.
  left; intuition.
  Qed.

  Lemma inter_1  :
   forall (s s' : t) (Hs : NoDup s) (Hs' : NoDup s') (x : elt),
   In x (inter s s') -> In x s.
  Proof.
  intros; cut (In x s /\ In x s'); [ intuition | apply inter_0; auto ].
  Qed.

  Lemma inter_2 :
   forall (s s' : t) (Hs : NoDup s) (Hs' : NoDup s') (x : elt),
   In x (inter s s') -> In x s'.
  Proof.
  intros; cut (In x s /\ In x s'); [ intuition | apply inter_0; auto ].
  Qed.

  Lemma inter_3 :
   forall (s s' : t) (Hs : NoDup s) (Hs' : NoDup s') (x : elt),
   In x s -> In x s' -> In x (inter s s').
  Proof.
  intros s s' Hs Hs' x.
  cut (((In x s /\ In x s')\/ In x (nil (A:=elt))) -> In x (inter s s')).
  intuition.
  unfold inter.
  set (acc := nil (A:=elt)) in *.
  assert (NoDup acc) by (unfold acc; auto).
  clearbody acc. 
  generalize H Hs' Hs; clear H Hs Hs'.
  generalize acc x s'; clear acc x s'.
  induction s; simpl; auto; intros.
  destruct H0; auto.
  destruct H0; inversion H0.
  inversion_clear Hs.
  case_eq (mem a s'); intros H3; apply IHs; auto.
  apply add_unique; auto.
  destruct H0.
  destruct H0.
  inversion_clear H0.
  right; apply add_1; auto.
  left; auto.
  right; apply add_2; auto.
  destruct H0; auto.
  destruct H0.
  inversion_clear H0; auto.
  absurd (In x s'); auto.
  red; intros.
  rewrite (mem_1 (In_eq H5 H0)) in H3.
  discriminate.
  Qed.

  Lemma diff_unique :
   forall (s s' : t) (Hs : NoDup s) (Hs' : NoDup s'), NoDup (diff s s').
  Proof.
  unfold diff; intros s s' Hs; generalize s Hs; clear Hs s.
  induction s'; simpl; auto; intros.
  inversion_clear Hs'.
  apply IHs'; auto.
  apply remove_unique; auto.
  Qed.  
  
  Lemma diff_0 :
   forall (s s' : t) (Hs : NoDup s) (Hs' : NoDup s') (x : elt),
   In x (diff s s') -> In x s /\ ~ In x s'.
  Proof.
  unfold diff; intros s s' Hs; generalize s Hs; clear Hs s.
  induction s'; simpl; auto; intros.
  inversion_clear Hs'.
  split; auto; intro H1; inversion H1.
  inversion_clear Hs'.
  destruct (IHs' (remove a s) (remove_unique Hs a) H1 x H).
  split. 
  eapply remove_3; eauto.
  red; intros.
  inversion_clear H4; auto.
  destruct (remove_1 Hs (X.eq_sym H5) H2).
  Qed.

  Lemma diff_1 :
   forall (s s' : t) (Hs : NoDup s) (Hs' : NoDup s') (x : elt),
   In x (diff s s') -> In x s.
  Proof.
  intros; cut (In x s /\ ~ In x s'); [ intuition | apply diff_0; auto]. 
  Qed.

  Lemma diff_2 :
   forall (s s' : t) (Hs : NoDup s) (Hs' : NoDup s') (x : elt),
   In x (diff s s') -> ~ In x s'.
  Proof.
  intros; cut (In x s /\ ~ In x s'); [ intuition | apply diff_0; auto]. 
  Qed.

  Lemma diff_3 :
   forall (s s' : t) (Hs : NoDup s) (Hs' : NoDup s') (x : elt),
   In x s -> ~ In x s' -> In x (diff s s').
  Proof.
  unfold diff; intros s s' Hs; generalize s Hs; clear Hs s.
  induction s'; simpl; auto; intros.
  inversion_clear Hs'.
  apply IHs'; auto.
  apply remove_unique; auto.
  apply remove_2; auto.
  Qed.  
  
  Lemma subset_1 :
   forall (s s' : t) (Hs : NoDup s) (Hs' : NoDup s'),
   Subset s s' -> subset s s' = true.
  Proof.
  unfold subset, Subset; intros.
  apply is_empty_1.
  unfold Empty; intros.
  intro.
  destruct (diff_2 Hs Hs' H0).
  apply H.
  eapply diff_1; eauto.
  Qed.

  Lemma subset_2 : forall (s s' : t)(Hs : NoDup s) (Hs' : NoDup s'), 
     subset s s' = true -> Subset s s'.
  Proof.
  unfold subset, Subset; intros.
  generalize (is_empty_2 H); clear H; unfold Empty; intros.
  generalize (@mem_1 s' a) (@mem_2 s' a); destruct (mem a s').
  intuition.
  intros.
  destruct (H a).
  apply diff_3; intuition.
  Qed.

  Lemma equal_1 :
   forall (s s' : t) (Hs : NoDup s) (Hs' : NoDup s'),
   Equal s s' -> equal s s' = true.
  Proof.
  unfold Equal, equal; intros.
  apply andb_true_intro; split; apply subset_1; firstorder.
  Qed.

  Lemma equal_2 : forall (s s' : t)(Hs : NoDup s) (Hs' : NoDup s'),  
     equal s s' = true -> Equal s s'.
  Proof.
  unfold Equal, equal; intros.
  destruct (andb_prop _ _ H); clear H.
  split; apply subset_2; auto.
  Qed.  

  Definition choose_1 :
    forall (s : t) (x : elt), choose s = Some x -> In x s.
  Proof.
  destruct s; simpl; intros; inversion H; auto.
  Qed.  

  Definition choose_2 : forall s : t, choose s = None -> Empty s.
  Proof.
  destruct s; simpl; intros.
  intros x H0; inversion H0.
  inversion H.
  Qed.  

  Lemma cardinal_1 :
   forall (s : t) (Hs : NoDup s), cardinal s = length (elements s).
  Proof.
  auto.
  Qed.

  Lemma filter_1 :
   forall (s : t) (x : elt) (f : elt -> bool),
   In x (filter f s) -> In x s.
  Proof.
  simple induction s; simpl.
  intros; inversion H.
  intros x l Hrec a f.
  case (f x); simpl.
  inversion_clear 1.
  constructor; auto.
  constructor 2; apply (Hrec a f); trivial.
  constructor 2; apply (Hrec a f); trivial.
  Qed.

   Lemma filter_2 :
    forall (s : t) (x : elt) (f : elt -> bool),
    compat_bool X.eq f -> In x (filter f s) -> f x = true.   
   Proof.
  simple induction s; simpl.
  intros; inversion H0.
  intros x l Hrec a f Hf.
  generalize (Hf x); case (f x); simpl; auto.
  inversion_clear 2; auto.
  symmetry; auto.
  Qed.
 
  Lemma filter_3 :
   forall (s : t) (x : elt) (f : elt -> bool),
   compat_bool X.eq f -> In x s -> f x = true -> In x (filter f s).     
  Proof.
  simple induction s; simpl.
  intros; inversion H0.
  intros x l Hrec a f Hf.
  generalize (Hf x); case (f x); simpl.
  inversion_clear 2; auto.
  inversion_clear 2; auto.
  rewrite <- (H a (X.eq_sym H1)); intros; discriminate.
  Qed.

  Lemma filter_unique :
   forall (s : t) (Hs : NoDup s) (f : elt -> bool), NoDup (filter f s).
  Proof.
  simple induction s; simpl.
  auto.
  intros x l Hrec Hs f; inversion_clear Hs.
  case (f x); auto.
  constructor; auto.
  intro H1; apply H.
  eapply filter_1; eauto.
  Qed.


  Lemma for_all_1 :
   forall (s : t) (f : elt -> bool),
   compat_bool X.eq f ->
   For_all (fun x => f x = true) s -> for_all f s = true.
  Proof. 
  simple induction s; simpl; auto; unfold For_all.
  intros x l Hrec f Hf. 
  generalize (Hf x); case (f x); simpl.
  auto.
  intros; rewrite (H x); auto.
  Qed.

  Lemma for_all_2 :
   forall (s : t) (f : elt -> bool),
   compat_bool X.eq f ->
   for_all f s = true -> For_all (fun x => f x = true) s.
  Proof. 
  simple induction s; simpl; auto; unfold For_all.
  intros; inversion H1.
  intros x l Hrec f Hf. 
  intros A a; intros. 
  assert (f x = true).
   generalize A; case (f x); auto.
  rewrite H0 in A; simpl in A.
  inversion_clear H; auto.
  rewrite (Hf a x); auto.
  Qed.

  Lemma exists_1 :
   forall (s : t) (f : elt -> bool),
   compat_bool X.eq f -> Exists (fun x => f x = true) s -> exists_ f s = true.
  Proof.
  simple induction s; simpl; auto; unfold Exists.
  intros.
  elim H0; intuition. 
  inversion H2.
  intros x l Hrec f Hf. 
  generalize (Hf x); case (f x); simpl.
  auto.
  destruct 2 as [a (A1,A2)].
  inversion_clear A1.
  rewrite <- (H a (X.eq_sym H0)) in A2; discriminate.
  apply Hrec; auto.
  exists a; auto.
  Qed.

  Lemma exists_2 :
   forall (s : t) (f : elt -> bool),
   compat_bool X.eq f -> exists_ f s = true -> Exists (fun x => f x = true) s.
  Proof. 
  simple induction s; simpl; auto; unfold Exists.
  intros; discriminate.
  intros x l Hrec f Hf.
  case_eq (f x); intros.
  exists x; auto.
  destruct (Hrec f Hf H0) as [a (A1,A2)].
  exists a; auto.
  Qed.

  Lemma partition_1 :
   forall (s : t) (f : elt -> bool),
   compat_bool X.eq f -> Equal (fst (partition f s)) (filter f s).
  Proof.
  simple induction s; simpl; auto; unfold Equal.
  firstorder.
  intros x l Hrec f Hf.
  generalize (Hrec f Hf); clear Hrec.
  case (partition f l); intros s1 s2; simpl; intros.
  case (f x); simpl; firstorder; inversion H0; intros; firstorder. 
  Qed.
   
  Lemma partition_2 :
   forall (s : t) (f : elt -> bool),
   compat_bool X.eq f ->
   Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
  Proof.
  simple induction s; simpl; auto; unfold Equal.
  firstorder.
  intros x l Hrec f Hf. 
  generalize (Hrec f Hf); clear Hrec.
  case (partition f l); intros s1 s2; simpl; intros.
  case (f x); simpl; firstorder; inversion H0; intros; firstorder. 
  Qed.

  Lemma partition_aux_1 : 
   forall (s : t) (Hs : NoDup s) (f : elt -> bool)(x:elt), 
    In x (fst (partition f s)) -> In x s.
  Proof.
  induction s; simpl; auto; intros.
  inversion_clear Hs.
  generalize (IHs H1 f x).
  destruct (f a); destruct (partition f s); simpl in *; auto.
  inversion_clear H; auto.
  Qed. 
     
  Lemma partition_aux_2 : 
   forall (s : t) (Hs : NoDup s) (f : elt -> bool)(x:elt), 
    In x (snd (partition f s)) -> In x s.
  Proof.
  induction s; simpl; auto; intros.
  inversion_clear Hs.
  generalize (IHs H1 f x).
  destruct (f a); destruct (partition f s); simpl in *; auto.
  inversion_clear H; auto.
  Qed. 
  
  Lemma partition_unique_1 :
   forall (s : t) (Hs : NoDup s) (f : elt -> bool), NoDup (fst (partition f s)).
  Proof.
  simple induction s; simpl.
  auto.
  intros x l Hrec Hs f; inversion_clear Hs.
  generalize (@partition_aux_1 _ H0 f x).
  generalize (Hrec H0 f).
  case (f x); case (partition f l); simpl; auto.
  Qed.
  
  Lemma partition_unique_2 :
   forall (s : t) (Hs : NoDup s) (f : elt -> bool), NoDup (snd (partition f s)).
  Proof.
  simple induction s; simpl.
  auto.
  intros x l Hrec Hs f; inversion_clear Hs.
  generalize (@partition_aux_2 _ H0 f x).
  generalize (Hrec H0 f).
  case (f x); case (partition f l); simpl; auto.
  Qed.

  Definition eq : t -> t -> Prop := Equal.

  Lemma eq_refl : forall s, eq s s. 
  Proof. firstorder. Qed.

  Lemma eq_sym : forall s s', eq s s' -> eq s' s.
  Proof. firstorder. Qed.

  Lemma eq_trans : 
   forall s s' s'', eq s s' -> eq s' s'' -> eq s s''.
  Proof. firstorder. Qed.

  Definition eq_dec : forall (s s':t)(Hs:NoDup s)(Hs':NoDup s'), 
   { eq s s' }+{ ~eq s s' }.
  Proof.
  unfold eq.
  induction s; intros s'.
  (* nil *)
   destruct s'; [left|right].
   firstorder.
   unfold not, Equal.
   intros H; generalize (H e); clear H.
   rewrite InA_nil, InA_cons; intuition.
  (* cons *)
   intros.
   case_eq (mem a s'); intros H; 
    [ destruct (IHs (remove a s')) as [H'|H']; 
      [ | | left|right]|right]; 
    clear IHs.
   inversion_clear Hs; auto.
   apply remove_unique; auto.
   (* In a s' /\ s [=] remove a s' *)
   generalize (mem_2 H); clear H; intro H.
   unfold Equal in *; intros b.
   rewrite InA_cons; split.
   destruct 1.
   apply In_eq with a; auto.
   rewrite H' in H0.
   apply remove_3 with a; auto.
   destruct (X.eq_dec b a); [left|right]; auto.
   rewrite H'.
   apply remove_2; auto.
   (* In a s' /\ ~ s [=] remove a s' *)
   generalize (mem_2 H); clear H; intro H.
   swap H'.
   unfold Equal in *; intros b.
   split; intros.
   apply remove_2; auto.
   inversion_clear Hs.
   swap H2; apply In_eq with b; auto.
   rewrite <- H0; rewrite InA_cons; auto.
   assert (In b s') by (apply remove_3 with a; auto).
   rewrite <- H0, InA_cons in H2; destruct H2; auto.
   elim (remove_1 Hs' (X.eq_sym H2) H1).
   (* ~ In a s' *)
   assert (~In a s').
    red; intro H'; rewrite (mem_1 H') in H; discriminate.
   swap H0.
   unfold Equal in *.
   rewrite <- H1.
   rewrite InA_cons; auto.
  Qed.

  End ForNotations.
End Raw.

(** * Encapsulation

   Now, in order to really provide a functor implementing [S], we 
   need to encapsulate everything into a type of lists without redundancy. *)

Module Make (X: DecidableType) <: S with Module E := X.

 Module Raw := Raw X. 
 Module E := X.

 Record slist : Set :=  {this :> Raw.t; unique : NoDupA E.eq this}.
 Definition t := slist. 
 Definition elt := E.t.
 
 Definition In (x : elt) (s : t) : Prop := InA E.eq x s.(this).
 Definition Equal (s s':t) : Prop := forall a : elt, In a s <-> In a s'.
 Definition Subset (s s':t) : Prop := forall a : elt, In a s -> In a s'.
 Definition Empty (s:t) : Prop := forall a : elt, ~ In a s.
 Definition For_all (P : elt -> Prop) (s : t) : Prop :=
   forall x : elt, In x s -> P x.
 Definition Exists (P : elt -> Prop) (s : t) : Prop := exists x : elt, In x s /\ P x.

 Definition mem (x : elt) (s : t) : bool := Raw.mem x s.
 Definition add (x : elt)(s : t) : t  := Build_slist (Raw.add_unique (unique s) x).
 Definition remove (x : elt)(s : t) : t := Build_slist (Raw.remove_unique (unique s) x).
 Definition singleton (x : elt) : t := Build_slist (Raw.singleton_unique x).
 Definition union (s s' : t) : t :=
   Build_slist (Raw.union_unique (unique s) (unique s')). 
 Definition inter (s s' : t) : t :=
   Build_slist (Raw.inter_unique (unique s) (unique s')). 
 Definition diff (s s' : t) : t :=
   Build_slist (Raw.diff_unique (unique s) (unique s')). 
 Definition equal (s s' : t) : bool := Raw.equal s s'. 
 Definition subset (s s' : t) : bool := Raw.subset s s'.
 Definition empty : t := Build_slist Raw.empty_unique.
 Definition is_empty (s : t) : bool := Raw.is_empty s.
 Definition elements (s : t) : list elt := Raw.elements s.
 Definition choose (s:t) : option elt := Raw.choose s.
 Definition fold (B : Type) (f : elt -> B -> B) (s : t) : B -> B := Raw.fold (B:=B) f s. 
 Definition cardinal (s : t) : nat := Raw.cardinal s.
 Definition filter (f : elt -> bool) (s : t) : t :=
   Build_slist (Raw.filter_unique (unique s) f).
 Definition for_all (f : elt -> bool) (s : t) : bool := Raw.for_all f s.
 Definition exists_ (f : elt -> bool) (s : t) : bool := Raw.exists_ f s.
 Definition partition (f : elt -> bool) (s : t) : t * t :=
   let p := Raw.partition f s in
   (Build_slist (this:=fst p) (Raw.partition_unique_1 (unique s) f),
   Build_slist (this:=snd p) (Raw.partition_unique_2 (unique s) f)).

 Section Spec. 
  Variable s s' : t.
  Variable x y : elt.

  Lemma In_1 : E.eq x y -> In x s -> In y s. 
  Proof. exact (fun H H' => Raw.In_eq H H'). Qed.
 
  Lemma mem_1 : In x s -> mem x s = true.
  Proof. exact (fun H => Raw.mem_1 H). Qed.
  Lemma mem_2 : mem x s = true -> In x s. 
  Proof. exact (fun H => Raw.mem_2 H). Qed.
 
  Lemma equal_1 : Equal s s' -> equal s s' = true.
  Proof. exact (Raw.equal_1 s.(unique) s'.(unique)). Qed.
  Lemma equal_2 : equal s s' = true -> Equal s s'.
  Proof. exact (Raw.equal_2 s.(unique) s'.(unique)). Qed.

  Lemma subset_1 : Subset s s' -> subset s s' = true.
  Proof. exact (Raw.subset_1 s.(unique) s'.(unique)). Qed.
  Lemma subset_2 : subset s s' = true -> Subset s s'.
  Proof. exact (Raw.subset_2 s.(unique) s'.(unique)). Qed.

  Lemma empty_1 : Empty empty.
  Proof. exact Raw.empty_1. Qed.

  Lemma is_empty_1 : Empty s -> is_empty s = true. 
  Proof. exact (fun H => Raw.is_empty_1 H). Qed.
  Lemma is_empty_2 : is_empty s = true -> Empty s.
  Proof. exact (fun H => Raw.is_empty_2 H). Qed.
 
  Lemma add_1 : E.eq x y -> In y (add x s).
  Proof. exact (fun H => Raw.add_1 s.(unique) H). Qed.
  Lemma add_2 : In y s -> In y (add x s).
  Proof. exact (fun H => Raw.add_2 s.(unique) x H). Qed.
  Lemma add_3 : ~ E.eq x y -> In y (add x s) -> In y s. 
  Proof. exact (fun H => Raw.add_3 s.(unique) H). Qed.

  Lemma remove_1 : E.eq x y -> ~ In y (remove x s).
  Proof. exact (fun H => Raw.remove_1 s.(unique) H). Qed.
  Lemma remove_2 : ~ E.eq x y -> In y s -> In y (remove x s).
  Proof. exact (fun H H' => Raw.remove_2 s.(unique) H H'). Qed.
  Lemma remove_3 : In y (remove x s) -> In y s.
  Proof. exact (fun H => Raw.remove_3 s.(unique) H). Qed.

  Lemma singleton_1 : In y (singleton x) -> E.eq x y. 
  Proof. exact (fun H => Raw.singleton_1 H). Qed.
  Lemma singleton_2 : E.eq x y -> In y (singleton x). 
  Proof. exact (fun H => Raw.singleton_2 H). Qed.

  Lemma union_1 : In x (union s s') -> In x s \/ In x s'.
  Proof. exact (fun H => Raw.union_1 s.(unique) s'.(unique) H). Qed.
  Lemma union_2 : In x s -> In x (union s s'). 
  Proof. exact (fun H => Raw.union_2 s.(unique) s'.(unique) H). Qed.
  Lemma union_3 : In x s' -> In x (union s s').
  Proof. exact (fun H => Raw.union_3 s.(unique) s'.(unique) H). Qed.

  Lemma inter_1 : In x (inter s s') -> In x s.
  Proof. exact (fun H => Raw.inter_1 s.(unique) s'.(unique) H). Qed.
  Lemma inter_2 : In x (inter s s') -> In x s'.
  Proof. exact (fun H => Raw.inter_2 s.(unique) s'.(unique) H). Qed.
  Lemma inter_3 : In x s -> In x s' -> In x (inter s s').
  Proof. exact (fun H => Raw.inter_3 s.(unique) s'.(unique) H). Qed.

  Lemma diff_1 : In x (diff s s') -> In x s. 
  Proof. exact (fun H => Raw.diff_1 s.(unique) s'.(unique) H). Qed.
  Lemma diff_2 : In x (diff s s') -> ~ In x s'.
  Proof. exact (fun H => Raw.diff_2 s.(unique) s'.(unique) H). Qed.
  Lemma diff_3 : In x s -> ~ In x s' -> In x (diff s s').
  Proof. exact (fun H => Raw.diff_3 s.(unique) s'.(unique) H). Qed.
 
  Lemma fold_1 : forall (A : Type) (i : A) (f : elt -> A -> A),
      fold f s i = fold_left (fun a e => f e a) (elements s) i.
  Proof. exact (Raw.fold_1 s.(unique)). Qed.

  Lemma cardinal_1 : cardinal s = length (elements s).
  Proof. exact (Raw.cardinal_1 s.(unique)). Qed.

  Section Filter.
  
  Variable f : elt -> bool.

  Lemma filter_1 : compat_bool E.eq f -> In x (filter f s) -> In x s. 
  Proof. exact (fun H => @Raw.filter_1 s x f). Qed.
  Lemma filter_2 : compat_bool E.eq f -> In x (filter f s) -> f x = true. 
  Proof. exact (@Raw.filter_2 s x f). Qed.
  Lemma filter_3 :
      compat_bool E.eq f -> In x s -> f x = true -> In x (filter f s).
  Proof. exact (@Raw.filter_3 s x f). Qed.

  Lemma for_all_1 :
      compat_bool E.eq f ->
      For_all (fun x => f x = true) s -> for_all f s = true.
  Proof. exact (@Raw.for_all_1 s f). Qed.
  Lemma for_all_2 :
      compat_bool E.eq f ->
      for_all f s = true -> For_all (fun x => f x = true) s.
  Proof. exact (@Raw.for_all_2 s f). Qed.

  Lemma exists_1 :
      compat_bool E.eq f ->
      Exists (fun x => f x = true) s -> exists_ f s = true.
  Proof. exact (@Raw.exists_1 s f). Qed.
  Lemma exists_2 :
      compat_bool E.eq f ->
      exists_ f s = true -> Exists (fun x => f x = true) s.
  Proof. exact (@Raw.exists_2 s f). Qed.

  Lemma partition_1 :
      compat_bool E.eq f -> Equal (fst (partition f s)) (filter f s).
  Proof. exact (@Raw.partition_1 s f). Qed.
  Lemma partition_2 :
      compat_bool E.eq f ->
      Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
  Proof. exact (@Raw.partition_2 s f). Qed.

  End Filter.

  Lemma elements_1 : In x s -> InA E.eq x (elements s).
  Proof. exact (fun H => Raw.elements_1 H). Qed.
  Lemma elements_2 : InA E.eq x (elements s) -> In x s.
  Proof. exact (fun H => Raw.elements_2 H). Qed.
  Lemma elements_3w : NoDupA E.eq (elements s).
  Proof. exact (Raw.elements_3w s.(unique)). Qed.

  Lemma choose_1 : choose s = Some x -> In x s.
  Proof. exact (fun H => Raw.choose_1 H). Qed.
  Lemma choose_2 : choose s = None -> Empty s.
  Proof. exact (fun H => Raw.choose_2 H). Qed.

 End Spec.

 Definition eq : t -> t -> Prop := Equal.

 Lemma eq_refl : forall s, eq s s. 
 Proof. firstorder. Qed.

 Lemma eq_sym : forall s s', eq s s' -> eq s' s.
 Proof. firstorder. Qed.

 Lemma eq_trans : 
  forall s s' s'', eq s s' -> eq s' s'' -> eq s s''.
 Proof. firstorder. Qed.

 Definition eq_dec : forall (s s':t), 
  { eq s s' }+{ ~eq s s' }.
 Proof. 
  intros s s'; exact (Raw.eq_dec s.(unique) s'.(unique)). 
 Qed.

End Make.

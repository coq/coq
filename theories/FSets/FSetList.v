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
    interface [FSetInterface.S] using strictly ordered list. *)

Require Export FSetInterface.
Set Implicit Arguments.
Unset Strict Implicit.

(** * Functions over lists

   First, we provide sets as lists which are not necessarily sorted.
   The specs are proved under the additional condition of being sorted.
   And the functions returning sets are proved to preserve this invariant. *)

Module Raw (X: OrderedType).

  Module MX := OrderedTypeFacts X.
  Import MX.

  Definition elt := X.t.
  Definition t := list elt.

  Definition empty : t := nil.

  Definition is_empty (l : t) : bool := if l then true else false.

  (** ** The set operations. *)

  Fixpoint mem (x : elt) (s : t) {struct s} : bool :=
    match s with
    | nil => false
    | y :: l =>
        match X.compare x y with
        | LT _ => false
        | EQ _ => true
        | GT _ => mem x l
        end
    end.

  Fixpoint add (x : elt) (s : t) {struct s} : t :=
    match s with
    | nil => x :: nil
    | y :: l =>
        match X.compare x y with
        | LT _ => x :: s
        | EQ _ => s
        | GT _ => y :: add x l
        end
    end.

  Definition singleton (x : elt) : t := x :: nil.

  Fixpoint remove (x : elt) (s : t) {struct s} : t :=
    match s with
    | nil => nil
    | y :: l =>
        match X.compare x y with
        | LT _ => s
        | EQ _ => l
        | GT _ => y :: remove x l
        end
    end.

  Fixpoint union (s : t) : t -> t :=
    match s with
    | nil => fun s' => s'
    | x :: l =>
        (fix union_aux (s' : t) : t :=
           match s' with
           | nil => s
           | x' :: l' =>
               match X.compare x x' with
               | LT _ => x :: union l s'
               | EQ _ => x :: union l l'
               | GT _ => x' :: union_aux l'
               end
           end)
    end.

  Fixpoint inter (s : t) : t -> t :=
    match s with
    | nil => fun _ => nil
    | x :: l =>
        (fix inter_aux (s' : t) : t :=
           match s' with
           | nil => nil
           | x' :: l' =>
               match X.compare x x' with
               | LT _ => inter l s'
               | EQ _ => x :: inter l l'
               | GT _ => inter_aux l'
               end
           end)
    end.

  Fixpoint diff (s : t) : t -> t :=
    match s with
    | nil => fun _ => nil
    | x :: l =>
        (fix diff_aux (s' : t) : t :=
           match s' with
           | nil => s
           | x' :: l' =>
               match X.compare x x' with
               | LT _ => x :: diff l s'
               | EQ _ => diff l l'
               | GT _ => diff_aux l'
               end
           end)
    end.

  Fixpoint equal (s : t) : t -> bool :=
    fun s' : t =>
    match s, s' with
    | nil, nil => true
    | x :: l, x' :: l' =>
        match X.compare x x' with
        | EQ _ => equal l l'
        | _ => false
        end
    | _, _ => false
    end.

  Fixpoint subset (s s' : t) {struct s'} : bool :=
    match s, s' with
    | nil, _ => true
    | x :: l, x' :: l' =>
        match X.compare x x' with
        | LT _ => false
        | EQ _ => subset l l'
        | GT _ => subset s l'
        end
    | _, _ => false
    end.

  Fixpoint fold (B : Type) (f : elt -> B -> B) (s : t) {struct s} :
   B -> B := fun i => match s with
                      | nil => i
                      | x :: l => fold f l (f x i)
                      end.

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

  Definition elements (x : t) : list elt := x.

  Definition min_elt (s : t) : option elt :=
    match s with
    | nil => None
    | x :: _ => Some x
    end.

  Fixpoint max_elt (s : t) : option elt :=
    match s with
    | nil => None
    | x :: nil => Some x
    | _ :: l => max_elt l
    end.

  Definition choose := min_elt.

  (** ** Proofs of set operation specifications. *)

  Section ForNotations.

  Notation Sort := (sort X.lt).
  Notation Inf := (lelistA X.lt).
  Notation In := (InA X.eq).

  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop) (s : t) := exists x, In x s /\ P x.

  Lemma mem_1 :
   forall (s : t) (Hs : Sort s) (x : elt), In x s -> mem x s = true.
  Proof.
  simple induction s; intros.
  inversion H.
  inversion_clear Hs.
  inversion_clear H0.
  simpl; elim_comp; trivial.
  simpl; elim_comp_gt x a; auto.
  apply Sort_Inf_In with l; trivial.
  Qed.

  Lemma mem_2 : forall (s : t) (x : elt), mem x s = true -> In x s.
  Proof.
  simple induction s.
  intros; inversion H.
  intros a l Hrec x.
  simpl.
  case (X.compare x a); intros; try discriminate; auto.
  Qed.

  Lemma add_Inf :
   forall (s : t) (x a : elt), Inf a s -> X.lt a x -> Inf a (add x s).
  Proof.
  simple induction s.
  simpl; intuition.
  simpl; intros; case (X.compare x a); intuition; inversion H0;
   intuition.
  Qed.
  Hint Resolve add_Inf.

  Lemma add_sort : forall (s : t) (Hs : Sort s) (x : elt), Sort (add x s).
  Proof.
  simple induction s.
  simpl; intuition.
  simpl; intros; case (X.compare x a); intuition; inversion_clear Hs;
   auto.
  Qed.

  Lemma add_1 :
   forall (s : t) (Hs : Sort s) (x y : elt), X.eq x y -> In y (add x s).
  Proof.
  simple induction s.
  simpl; intuition.
  simpl; intros; case (X.compare x a); inversion_clear Hs; auto.
  constructor; apply X.eq_trans with x; auto.
  Qed.

  Lemma add_2 :
   forall (s : t) (Hs : Sort s) (x y : elt), In y s -> In y (add x s).
  Proof.
  simple induction s.
  simpl; intuition.
  simpl; intros; case (X.compare x a); intuition.
  inversion_clear Hs; inversion_clear H0; auto.
  Qed.

  Lemma add_3 :
   forall (s : t) (Hs : Sort s) (x y : elt),
   ~ X.eq x y -> In y (add x s) -> In y s.
  Proof.
  simple induction s.
  simpl; inversion_clear 3; auto; order.
  simpl; intros a l Hrec Hs x y; case (X.compare x a); intros;
   inversion_clear H0; inversion_clear Hs; auto.
  order.
  constructor 2; apply Hrec with x; auto.
  Qed.

  Lemma remove_Inf :
   forall (s : t) (Hs : Sort s) (x a : elt), Inf a s -> Inf a (remove x s).
  Proof.
  simple induction s.
  simpl; intuition.
  simpl; intros; case (X.compare x a); intuition; inversion_clear H0; auto.
  inversion_clear Hs; apply Inf_lt with a; auto.
  Qed.
  Hint Resolve remove_Inf.

  Lemma remove_sort :
   forall (s : t) (Hs : Sort s) (x : elt), Sort (remove x s).
  Proof.
  simple induction s.
  simpl; intuition.
  simpl; intros; case (X.compare x a); intuition; inversion_clear Hs; auto.
  Qed.

  Lemma remove_1 :
   forall (s : t) (Hs : Sort s) (x y : elt), X.eq x y -> ~ In y (remove x s).
  Proof.
  simple induction s.
  simpl; red; intros; inversion H0.
  simpl; intros; case (X.compare x a); intuition; inversion_clear Hs.
  inversion_clear H1.
  order.
  generalize (Sort_Inf_In H2 H3 H4); order.
  generalize (Sort_Inf_In H2 H3 H1); order.
  inversion_clear H1.
  order.
  apply (H H2 _ _ H0 H4).
  Qed.

  Lemma remove_2 :
   forall (s : t) (Hs : Sort s) (x y : elt),
   ~ X.eq x y -> In y s -> In y (remove x s).
  Proof.
  simple induction s.
  simpl; intuition.
  simpl; intros; case (X.compare x a); intuition; inversion_clear Hs;
   inversion_clear H1; auto.
  destruct H0; apply X.eq_trans with a; auto.
  Qed.

  Lemma remove_3 :
   forall (s : t) (Hs : Sort s) (x y : elt), In y (remove x s) -> In y s.
  Proof.
  simple induction s.
  simpl; intuition.
  simpl; intros a l Hrec Hs x y; case (X.compare x a); intuition.
  inversion_clear Hs; inversion_clear H; auto.
  constructor 2; apply Hrec with x; auto.
  Qed.

  Lemma singleton_sort : forall x : elt, Sort (singleton x).
  Proof.
  unfold singleton; simpl; auto.
  Qed.

  Lemma singleton_1 : forall x y : elt, In y (singleton x) -> X.eq x y.
  Proof.
  unfold singleton; simpl; intuition.
  inversion_clear H; auto; inversion H0.
  Qed.

  Lemma singleton_2 : forall x y : elt, X.eq x y -> In y (singleton x).
  Proof.
  unfold singleton; simpl; auto.
  Qed.

  Ltac DoubleInd :=
    simple induction s;
     [ simpl; auto; try solve [ intros; inversion H ]
     | intros x l Hrec; simple induction s';
        [ simpl; auto; try solve [ intros; inversion H ]
        | intros x' l' Hrec' Hs Hs'; inversion Hs; inversion Hs'; subst;
           simpl ] ].

  Lemma union_Inf :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (a : elt),
   Inf a s -> Inf a s' -> Inf a (union s s').
  Proof.
  DoubleInd.
  intros i His His'; inversion_clear His; inversion_clear His'.
  case (X.compare x x'); auto.
  Qed.
  Hint Resolve union_Inf.

  Lemma union_sort :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'), Sort (union s s').
  Proof.
  DoubleInd; case (X.compare x x'); intuition; constructor; auto.
  apply Inf_eq with x'; trivial; apply union_Inf; trivial; apply Inf_eq with x; auto.
  change (Inf x' (union (x :: l) l')); auto.
  Qed.

  Lemma union_1 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
   In x (union s s') -> In x s \/ In x s'.
  Proof.
  DoubleInd; case (X.compare x x'); intuition; inversion_clear H; intuition.
  elim (Hrec (x' :: l') H1 Hs' x0); intuition.
  elim (Hrec l' H1 H5 x0); intuition.
  elim (H0 x0); intuition.
  Qed.

  Lemma union_2 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
   In x s -> In x (union s s').
  Proof.
  DoubleInd.
  intros i Hi; case (X.compare x x'); intuition; inversion_clear Hi; auto.
  Qed.

  Lemma union_3 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
   In x s' -> In x (union s s').
  Proof.
  DoubleInd.
  intros i Hi; case (X.compare x x'); inversion_clear Hi; intuition.
  constructor; apply X.eq_trans with x'; auto.
  Qed.

  Lemma inter_Inf :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (a : elt),
   Inf a s -> Inf a s' -> Inf a (inter s s').
  Proof.
  DoubleInd.
  intros i His His'; inversion His; inversion His'; subst.
  case (X.compare x x'); intuition.
  apply Inf_lt with x; auto.
  apply H3; auto.
  apply Inf_lt with x'; auto.
  Qed.
  Hint Resolve inter_Inf.

  Lemma inter_sort :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'), Sort (inter s s').
  Proof.
  DoubleInd; case (X.compare x x'); auto.
  constructor; auto.
  apply Inf_eq with x'; trivial; apply inter_Inf; trivial; apply Inf_eq with x; auto.
  Qed.

  Lemma inter_1 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
   In x (inter s s') -> In x s.
  Proof.
  DoubleInd; case (X.compare x x'); intuition.
  constructor 2; apply Hrec with (x'::l'); auto.
  inversion_clear H; auto.
  constructor 2; apply Hrec with l'; auto.
  Qed.

  Lemma inter_2 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
   In x (inter s s') -> In x s'.
  Proof.
  DoubleInd; case (X.compare x x'); intuition; inversion_clear H.
  constructor 1; apply X.eq_trans with x; auto.
  constructor 2; auto.
  Qed.

  Lemma inter_3 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
   In x s -> In x s' -> In x (inter s s').
  Proof.
  DoubleInd.
  intros i His His'; elim (X.compare x x'); intuition.

  inversion_clear His; auto.
  generalize (Sort_Inf_In Hs' (cons_leA _ _ _ _ l0) His'); order.

  inversion_clear His; auto; inversion_clear His'; auto.
  constructor; apply X.eq_trans with x'; auto.

  change (In i (inter (x :: l) l')).
  inversion_clear His'; auto.
  generalize (Sort_Inf_In Hs (cons_leA _ _ _ _ l0) His); order.
  Qed.

  Lemma diff_Inf :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (a : elt),
   Inf a s -> Inf a s' -> Inf a (diff s s').
  Proof.
  DoubleInd.
  intros i His His'; inversion His; inversion His'.
  case (X.compare x x'); intuition.
  apply Hrec; trivial.
  apply Inf_lt with x; auto.
  apply Inf_lt with x'; auto.
  apply H10; trivial.
  apply Inf_lt with x'; auto.
  Qed.
  Hint Resolve diff_Inf.

  Lemma diff_sort :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'), Sort (diff s s').
  Proof.
  DoubleInd; case (X.compare x x'); auto.
  Qed.

  Lemma diff_1 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
   In x (diff s s') -> In x s.
  Proof.
  DoubleInd; case (X.compare x x'); intuition.
  inversion_clear H; auto.
  constructor 2; apply Hrec with (x'::l'); auto.
  constructor 2; apply Hrec with l'; auto.
  Qed.

  Lemma diff_2 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
   In x (diff s s') -> ~ In x s'.
  Proof.
  DoubleInd.
  intros; intro Abs; inversion Abs.
  case (X.compare x x'); intuition.

  inversion_clear H.
  generalize (Sort_Inf_In Hs' (cons_leA _ _ _ _ l0) H3); order.
  apply Hrec with (x'::l') x0; auto.

  inversion_clear H3.
  generalize (Sort_Inf_In H1 H2 (diff_1 H1 H5 H)); order.
  apply Hrec with l' x0; auto.

  inversion_clear H3.
  generalize (Sort_Inf_In Hs (cons_leA _ _ _ _ l0) (diff_1 Hs H5 H)); order.
  apply H0 with x0; auto.
  Qed.

  Lemma diff_3 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
   In x s -> ~ In x s' -> In x (diff s s').
  Proof.
  DoubleInd.
  intros i His His'; elim (X.compare x x'); intuition; inversion_clear His; auto.
  elim His'; constructor; apply X.eq_trans with x; auto.
  Qed.

  Lemma equal_1 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'),
   Equal s s' -> equal s s' = true.
  Proof.
  simple induction s; unfold Equal.
  intro s'; case s'; auto.
  simpl; intuition.
  elim (H e); intros; assert (A : In e nil); auto; inversion A.
  intros x l Hrec s'.
  case s'.
  intros; elim (H x); intros; assert (A : In x nil); auto; inversion A.
  intros x' l' Hs Hs'; inversion Hs; inversion Hs'; subst.
  simpl; case (X.compare x); intros; auto.

  elim (H x); intros.
  assert (A : In x (x' :: l')); auto; inversion_clear A.
  order.
  generalize (Sort_Inf_In H5 H6 H4); order.

  apply Hrec; intuition; elim (H a); intros.
  assert (A : In a (x' :: l')); auto; inversion_clear A; auto.
  generalize (Sort_Inf_In H1 H2 H0); order.
  assert (A : In a (x :: l)); auto; inversion_clear A; auto.
  generalize (Sort_Inf_In H5 H6 H0); order.

  elim (H x'); intros.
  assert (A : In x' (x :: l)); auto; inversion_clear A.
  order.
  generalize (Sort_Inf_In H1 H2 H4); order.
  Qed.

  Lemma equal_2 : forall s s' : t, equal s s' = true -> Equal s s'.
  Proof.
  simple induction s; unfold Equal.
  intro s'; case s'; intros.
  intuition.
  simpl in H; discriminate H.
  intros x l Hrec s'.
  case s'.
  intros; simpl in H; discriminate.
  intros x' l'; simpl; case (X.compare x); intros; auto; try discriminate.
  elim (Hrec l' H a); intuition; inversion_clear H2; auto.
  constructor; apply X.eq_trans with x; auto.
  constructor; apply X.eq_trans with x'; auto.
  Qed.

  Lemma subset_1 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'),
   Subset s s' -> subset s s' = true.
  Proof.
  intros s s'; generalize s' s; clear s s'.
  simple induction s'; unfold Subset.
  intro s; case s; auto.
  intros; elim (H e); intros; assert (A : In e nil); auto; inversion A.
  intros x' l' Hrec s; case s.
  simpl; auto.
  intros x l Hs Hs'; inversion Hs; inversion Hs'; subst.
  simpl; case (X.compare x); intros; auto.

  assert (A : In x (x' :: l')); auto; inversion_clear A.
  order.
  generalize (Sort_Inf_In H5 H6 H0); order.

  apply Hrec; intuition.
  assert (A : In a (x' :: l')); auto; inversion_clear A; auto.
  generalize (Sort_Inf_In H1 H2 H0); order.

  apply Hrec; intuition.
  assert (A : In a (x' :: l')); auto; inversion_clear A; auto.
  inversion_clear H0.
  order.
  generalize (Sort_Inf_In H1 H2 H4); order.
  Qed.

  Lemma subset_2 : forall s s' : t, subset s s' = true -> Subset s s'.
  Proof.
  intros s s'; generalize s' s; clear s s'.
  simple induction s'; unfold Subset.
  intro s; case s; auto.
  simpl; intros; discriminate H.
  intros x' l' Hrec s; case s.
  intros; inversion H0.
  intros x l; simpl; case (X.compare x); intros; auto.
  discriminate H.
  inversion_clear H0.
  constructor; apply X.eq_trans with x; auto.
  constructor 2; apply Hrec with l; auto.
  constructor 2; apply Hrec with (x::l); auto.
  Qed.

  Lemma empty_sort : Sort empty.
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

  Lemma elements_3 : forall (s : t) (Hs : Sort s), Sort (elements s).
  Proof.
  unfold elements; auto.
  Qed.

  Lemma elements_3w : forall (s : t) (Hs : Sort s), NoDupA X.eq (elements s).
  Proof.
  unfold elements; auto.
  Qed.

  Lemma min_elt_1 : forall (s : t) (x : elt), min_elt s = Some x -> In x s.
  Proof.
  intro s; case s; simpl; intros; inversion H; auto.
  Qed.

  Lemma min_elt_2 :
   forall (s : t) (Hs : Sort s) (x y : elt),
   min_elt s = Some x -> In y s -> ~ X.lt y x.
  Proof.
  simple induction s; simpl.
  intros; inversion H.
  intros a l; case l; intros; inversion H0; inversion_clear H1; subst.
  order.
  inversion H2.
  order.
  inversion_clear Hs.
  inversion_clear H3.
  generalize (H H1 e y (refl_equal (Some e)) H2); order.
  Qed.

  Lemma min_elt_3 : forall s : t, min_elt s = None -> Empty s.
  Proof.
  unfold Empty; intro s; case s; simpl; intuition;
   inversion H; inversion H0.
  Qed.

  Lemma max_elt_1 : forall (s : t) (x : elt), max_elt s = Some x -> In x s.
  Proof.
  simple induction s; simpl.
  intros; inversion H.
  intros x l; case l; simpl.
  intuition.
  inversion H0; auto.
  intros.
  constructor 2; apply (H _ H0).
  Qed.

  Lemma max_elt_2 :
   forall (s : t) (Hs : Sort s) (x y : elt),
   max_elt s = Some x -> In y s -> ~ X.lt x y.
  Proof.
  simple induction s; simpl.
  intros; inversion H.
  intros x l; case l; simpl.
  intuition.
  inversion H0; subst.
  inversion_clear H1.
  order.
  inversion H3.
  intros; inversion_clear Hs; inversion_clear H3; inversion_clear H1.
  assert (In e (e::l0)) by auto.
  generalize (H H2 x0 e H0 H1); order.
  generalize (H H2 x0 y H0 H3); order.
  Qed.

  Lemma max_elt_3 : forall s : t, max_elt s = None -> Empty s.
  Proof.
  unfold Empty; simple induction s; simpl.
  red; intros; inversion H0.
  intros x l; case l; simpl; intros.
  inversion H0.
  elim (H H0 e); auto.
  Qed.

  Definition choose_1 :
    forall (s : t) (x : elt), choose s = Some x -> In x s := min_elt_1.

  Definition choose_2 : forall s : t, choose s = None -> Empty s := min_elt_3.

  Lemma choose_3: forall s s', Sort s -> Sort s' -> forall x x',
   choose s = Some x -> choose s' = Some x' -> Equal s s' -> X.eq x x'.
  Proof.
   unfold choose, Equal; intros s s' Hs Hs' x x' Hx Hx' H.
   assert (~X.lt x x').
    apply min_elt_2 with s'; auto.
    rewrite <-H; auto using min_elt_1.
   assert (~X.lt x' x).
    apply min_elt_2 with s; auto.
    rewrite H; auto using min_elt_1.
   destruct (X.compare x x'); intuition.
  Qed.

  Lemma fold_1 :
   forall (s : t) (Hs : Sort s) (A : Type) (i : A) (f : elt -> A -> A),
   fold f s i = fold_left (fun a e => f e a) (elements s) i.
  Proof.
  induction s.
  simpl; trivial.
  intros.
  inversion_clear Hs.
  simpl; auto.
  Qed.

  Lemma cardinal_1 :
   forall (s : t) (Hs : Sort s),
   cardinal s = length (elements s).
  Proof.
  auto.
  Qed.

  Lemma filter_Inf :
   forall (s : t) (Hs : Sort s) (x : elt) (f : elt -> bool),
   Inf x s -> Inf x (filter f s).
  Proof.
  simple induction s; simpl.
  intuition.
  intros x l Hrec Hs a f Ha; inversion_clear Hs; inversion_clear Ha.
  case (f x).
  constructor; auto.
  apply Hrec; auto.
  apply Inf_lt with x; auto.
  Qed.

  Lemma filter_sort :
   forall (s : t) (Hs : Sort s) (f : elt -> bool), Sort (filter f s).
  Proof.
  simple induction s; simpl.
  auto.
  intros x l Hrec Hs f; inversion_clear Hs.
  case (f x); auto.
  constructor; auto.
  apply filter_Inf; auto.
  Qed.

  Lemma filter_1 :
   forall (s : t) (x : elt) (f : elt -> bool),
   compat_bool X.eq f -> In x (filter f s) -> In x s.
  Proof.
  simple induction s; simpl.
  intros; inversion H0.
  intros x l Hrec a f Hf.
  case (f x); simpl.
  inversion_clear 1.
  constructor; auto.
  constructor 2; apply (Hrec a f Hf); trivial.
  constructor 2; apply (Hrec a f Hf); trivial.
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

  Lemma partition_Inf_1 :
   forall (s : t) (Hs : Sort s) (f : elt -> bool) (x : elt),
   Inf x s -> Inf x (fst (partition f s)).
  Proof.
  simple induction s; simpl.
  intuition.
  intros x l Hrec Hs f a Ha; inversion_clear Hs; inversion_clear Ha.
  generalize (Hrec H f a).
  case (f x); case (partition f l); simpl.
  auto.
  intros; apply H2; apply Inf_lt with x; auto.
  Qed.

  Lemma partition_Inf_2 :
   forall (s : t) (Hs : Sort s) (f : elt -> bool) (x : elt),
   Inf x s -> Inf x (snd (partition f s)).
  Proof.
  simple induction s; simpl.
  intuition.
  intros x l Hrec Hs f a Ha; inversion_clear Hs; inversion_clear Ha.
  generalize (Hrec H f a).
  case (f x); case (partition f l); simpl.
  intros; apply H2; apply Inf_lt with x; auto.
  auto.
  Qed.

  Lemma partition_sort_1 :
   forall (s : t) (Hs : Sort s) (f : elt -> bool), Sort (fst (partition f s)).
  Proof.
  simple induction s; simpl.
  auto.
  intros x l Hrec Hs f; inversion_clear Hs.
  generalize (Hrec H f); generalize (partition_Inf_1 H f).
  case (f x); case (partition f l); simpl; auto.
  Qed.

  Lemma partition_sort_2 :
   forall (s : t) (Hs : Sort s) (f : elt -> bool), Sort (snd (partition f s)).
  Proof.
  simple induction s; simpl.
  auto.
  intros x l Hrec Hs f; inversion_clear Hs.
  generalize (Hrec H f); generalize (partition_Inf_2 H f).
  case (f x); case (partition f l); simpl; auto.
  Qed.

  Lemma partition_1 :
   forall (s : t) (f : elt -> bool),
   compat_bool X.eq f -> Equal (fst (partition f s)) (filter f s).
  Proof.
  simple induction s; simpl; auto; unfold Equal.
  split; auto.
  intros x l Hrec f Hf.
  generalize (Hrec f Hf); clear Hrec.
  destruct (partition f l) as [s1 s2]; simpl; intros.
  case (f x); simpl; auto.
  split; inversion_clear 1; auto.
  constructor 2; rewrite <- H; auto.
  constructor 2; rewrite H; auto.
  Qed.

  Lemma partition_2 :
   forall (s : t) (f : elt -> bool),
   compat_bool X.eq f ->
   Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
  Proof.
  simple induction s; simpl; auto; unfold Equal.
  split; auto.
  intros x l Hrec f Hf.
  generalize (Hrec f Hf); clear Hrec.
  destruct (partition f l) as [s1 s2]; simpl; intros.
  case (f x); simpl; auto.
  split; inversion_clear 1; auto.
  constructor 2; rewrite <- H; auto.
  constructor 2; rewrite H; auto.
  Qed.

  Definition eq : t -> t -> Prop := Equal.

  Lemma eq_refl : forall s : t, eq s s.
  Proof.
  unfold eq, Equal; intuition.
  Qed.

  Lemma eq_sym : forall s s' : t, eq s s' -> eq s' s.
  Proof.
  unfold eq, Equal; intros; destruct (H a); intuition.
  Qed.

  Lemma eq_trans : forall s s' s'' : t, eq s s' -> eq s' s'' -> eq s s''.
  Proof.
  unfold eq, Equal; intros; destruct (H a); destruct (H0 a); intuition.
  Qed.

  Inductive lt : t -> t -> Prop :=
    | lt_nil : forall (x : elt) (s : t), lt nil (x :: s)
    | lt_cons_lt :
        forall (x y : elt) (s s' : t), X.lt x y -> lt (x :: s) (y :: s')
    | lt_cons_eq :
        forall (x y : elt) (s s' : t),
        X.eq x y -> lt s s' -> lt (x :: s) (y :: s').
  Hint Constructors lt.

  Lemma lt_trans : forall s s' s'' : t, lt s s' -> lt s' s'' -> lt s s''.
  Proof.
  intros s s' s'' H; generalize s''; clear s''; elim H.
  intros x l s'' H'; inversion_clear H'; auto.
  intros x x' l l' E s'' H'; inversion_clear H'; auto.
  constructor; apply X.lt_trans with x'; auto.
  constructor; apply lt_eq with x'; auto.
  intros.
  inversion_clear H3.
  constructor; apply eq_lt with y; auto.
  constructor 3; auto; apply X.eq_trans with y; auto.
  Qed.

  Lemma lt_not_eq :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'), lt s s' -> ~ eq s s'.
  Proof.
  unfold eq, Equal.
  intros s s' Hs Hs' H; generalize Hs Hs'; clear Hs Hs'; elim H; intros; intro.
  elim (H0 x); intros.
  assert (X : In x nil); auto; inversion X.
  inversion_clear Hs; inversion_clear Hs'.
  elim (H1 x); intros.
  assert (X : In x (y :: s'0)); auto; inversion_clear X.
  order.
  generalize (Sort_Inf_In H4 H5 H8); order.
  inversion_clear Hs; inversion_clear Hs'.
  elim H2; auto; split; intros.
  generalize (Sort_Inf_In H4 H5 H8); intros.
  elim (H3 a); intros.
  assert (X : In a (y :: s'0)); auto; inversion_clear X; auto.
  order.
  generalize (Sort_Inf_In H6 H7 H8); intros.
  elim (H3 a); intros.
  assert (X : In a (x :: s0)); auto; inversion_clear X; auto.
  order.
  Qed.

  Definition compare :
    forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'), Compare lt eq s s'.
  Proof.
  simple induction s.
  intros; case s'.
  constructor 2; apply eq_refl.
  constructor 1; auto.
  intros a l Hrec s'; case s'.
  constructor 3; auto.
  intros a' l' Hs Hs'.
  case (X.compare a a'); [ constructor 1 | idtac | constructor 3 ]; auto.
  elim (Hrec l');
   [ constructor 1
   | constructor 2
   | constructor 3
   | inversion Hs
   | inversion Hs' ]; auto.
  generalize e; unfold eq, Equal; intuition; inversion_clear H.
  constructor; apply X.eq_trans with a; auto.
  destruct (e1 a0); auto.
  constructor; apply X.eq_trans with a'; auto.
  destruct (e1 a0); auto.
  Defined.

  End ForNotations.
  Hint Constructors lt.

End Raw.

(** * Encapsulation

   Now, in order to really provide a functor implementing [S], we
   need to encapsulate everything into a type of strictly ordered lists. *)

Module Make (X: OrderedType) <: S with Module E := X.

 Module Raw := Raw X.
 Module E := X.

 Record slist := {this :> Raw.t; sorted : sort E.lt this}.
 Definition t := slist.
 Definition elt := E.t.

 Definition In (x : elt) (s : t) : Prop := InA E.eq x s.(this).
 Definition Equal (s s':t) : Prop := forall a : elt, In a s <-> In a s'.
 Definition Subset (s s':t) : Prop := forall a : elt, In a s -> In a s'.
 Definition Empty (s:t) : Prop := forall a : elt, ~ In a s.
 Definition For_all (P : elt -> Prop)(s:t) : Prop := forall x, In x s -> P x.
 Definition Exists (P : elt -> Prop)(s:t) : Prop := exists x, In x s /\ P x.

 Definition mem (x : elt) (s : t) : bool := Raw.mem x s.
 Definition add (x : elt)(s : t) : t := Build_slist (Raw.add_sort (sorted s) x).
 Definition remove (x : elt)(s : t) : t := Build_slist (Raw.remove_sort (sorted s) x).
 Definition singleton (x : elt) : t  := Build_slist (Raw.singleton_sort x).
 Definition union (s s' : t) : t :=
   Build_slist (Raw.union_sort (sorted s) (sorted s')).
 Definition inter (s s' : t) : t :=
   Build_slist (Raw.inter_sort (sorted s) (sorted s')).
 Definition diff (s s' : t) : t :=
   Build_slist (Raw.diff_sort (sorted s) (sorted s')).
 Definition equal (s s' : t) : bool := Raw.equal s s'.
 Definition subset (s s' : t) : bool := Raw.subset s s'.
 Definition empty : t := Build_slist Raw.empty_sort.
 Definition is_empty (s : t) : bool := Raw.is_empty s.
 Definition elements (s : t) : list elt := Raw.elements s.
 Definition min_elt (s : t) : option elt := Raw.min_elt s.
 Definition max_elt (s : t) : option elt := Raw.max_elt s.
 Definition choose (s : t) : option elt  := Raw.choose s.
 Definition fold (B : Type) (f : elt -> B -> B) (s : t) : B -> B := Raw.fold (B:=B) f s.
 Definition cardinal (s : t) : nat := Raw.cardinal s.
 Definition filter (f : elt -> bool) (s : t) : t :=
   Build_slist (Raw.filter_sort (sorted s) f).
 Definition for_all (f : elt -> bool) (s : t) : bool := Raw.for_all f s.
 Definition exists_ (f : elt -> bool) (s : t) : bool := Raw.exists_ f s.
 Definition partition (f : elt -> bool) (s : t) : t * t :=
   let p := Raw.partition f s in
   (Build_slist (this:=fst p) (Raw.partition_sort_1 (sorted s) f),
   Build_slist (this:=snd p) (Raw.partition_sort_2 (sorted s) f)).
 Definition eq (s s' : t) : Prop := Raw.eq s s'.
 Definition lt (s s' : t) : Prop := Raw.lt s s'.

 Section Spec.
  Variable s s' s'': t.
  Variable x y : elt.

  Lemma In_1 : E.eq x y -> In x s -> In y s.
  Proof. exact (fun H H' => Raw.MX.In_eq H H'). Qed.

  Lemma mem_1 : In x s -> mem x s = true.
  Proof. exact (fun H => Raw.mem_1 s.(sorted) H). Qed.
  Lemma mem_2 : mem x s = true -> In x s.
  Proof. exact (fun H => Raw.mem_2 H). Qed.

  Lemma equal_1 : Equal s s' -> equal s s' = true.
  Proof. exact (Raw.equal_1 s.(sorted) s'.(sorted)). Qed.
  Lemma equal_2 : equal s s' = true -> Equal s s'.
  Proof. exact (fun H => Raw.equal_2 H). Qed.

  Lemma subset_1 : Subset s s' -> subset s s' = true.
  Proof. exact (Raw.subset_1 s.(sorted) s'.(sorted)). Qed.
  Lemma subset_2 : subset s s' = true -> Subset s s'.
  Proof. exact (fun H => Raw.subset_2 H). Qed.

  Lemma empty_1 : Empty empty.
  Proof. exact Raw.empty_1. Qed.

  Lemma is_empty_1 : Empty s -> is_empty s = true.
  Proof. exact (fun H => Raw.is_empty_1 H). Qed.
  Lemma is_empty_2 : is_empty s = true -> Empty s.
  Proof. exact (fun H => Raw.is_empty_2 H). Qed.

  Lemma add_1 : E.eq x y -> In y (add x s).
  Proof. exact (fun H => Raw.add_1 s.(sorted) H). Qed.
  Lemma add_2 : In y s -> In y (add x s).
  Proof. exact (fun H => Raw.add_2 s.(sorted) x H). Qed.
  Lemma add_3 : ~ E.eq x y -> In y (add x s) -> In y s.
  Proof. exact (fun H => Raw.add_3 s.(sorted) H). Qed.

  Lemma remove_1 : E.eq x y -> ~ In y (remove x s).
  Proof. exact (fun H => Raw.remove_1 s.(sorted) H). Qed.
  Lemma remove_2 : ~ E.eq x y -> In y s -> In y (remove x s).
  Proof. exact (fun H H' => Raw.remove_2 s.(sorted) H H'). Qed.
  Lemma remove_3 : In y (remove x s) -> In y s.
  Proof. exact (fun H => Raw.remove_3 s.(sorted) H). Qed.

  Lemma singleton_1 : In y (singleton x) -> E.eq x y.
  Proof. exact (fun H => Raw.singleton_1 H). Qed.
  Lemma singleton_2 : E.eq x y -> In y (singleton x).
  Proof. exact (fun H => Raw.singleton_2 H). Qed.

  Lemma union_1 : In x (union s s') -> In x s \/ In x s'.
  Proof. exact (fun H => Raw.union_1 s.(sorted) s'.(sorted) H). Qed.
  Lemma union_2 : In x s -> In x (union s s').
  Proof. exact (fun H => Raw.union_2 s.(sorted) s'.(sorted) H). Qed.
  Lemma union_3 : In x s' -> In x (union s s').
  Proof. exact (fun H => Raw.union_3 s.(sorted) s'.(sorted) H). Qed.

  Lemma inter_1 : In x (inter s s') -> In x s.
  Proof. exact (fun H => Raw.inter_1 s.(sorted) s'.(sorted) H). Qed.
  Lemma inter_2 : In x (inter s s') -> In x s'.
  Proof. exact (fun H => Raw.inter_2 s.(sorted) s'.(sorted) H). Qed.
  Lemma inter_3 : In x s -> In x s' -> In x (inter s s').
  Proof. exact (fun H => Raw.inter_3 s.(sorted) s'.(sorted) H). Qed.

  Lemma diff_1 : In x (diff s s') -> In x s.
  Proof. exact (fun H => Raw.diff_1 s.(sorted) s'.(sorted) H). Qed.
  Lemma diff_2 : In x (diff s s') -> ~ In x s'.
  Proof. exact (fun H => Raw.diff_2 s.(sorted) s'.(sorted) H). Qed.
  Lemma diff_3 : In x s -> ~ In x s' -> In x (diff s s').
  Proof. exact (fun H => Raw.diff_3 s.(sorted) s'.(sorted) H). Qed.

  Lemma fold_1 : forall (A : Type) (i : A) (f : elt -> A -> A),
      fold f s i = fold_left (fun a e => f e a) (elements s) i.
  Proof. exact (Raw.fold_1 s.(sorted)). Qed.

  Lemma cardinal_1 : cardinal s = length (elements s).
  Proof. exact (Raw.cardinal_1 s.(sorted)). Qed.

  Section Filter.

  Variable f : elt -> bool.

  Lemma filter_1 : compat_bool E.eq f -> In x (filter f s) -> In x s.
  Proof. exact (@Raw.filter_1 s x f). Qed.
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
  Lemma elements_3 : sort E.lt (elements s).
  Proof. exact (Raw.elements_3 s.(sorted)). Qed.
  Lemma elements_3w : NoDupA E.eq (elements s).
  Proof. exact (Raw.elements_3w s.(sorted)). Qed.

  Lemma min_elt_1 : min_elt s = Some x -> In x s.
  Proof. exact (fun H => Raw.min_elt_1 H). Qed.
  Lemma min_elt_2 : min_elt s = Some x -> In y s -> ~ E.lt y x.
  Proof. exact (fun H => Raw.min_elt_2 s.(sorted) H). Qed.
  Lemma min_elt_3 : min_elt s = None -> Empty s.
  Proof. exact (fun H => Raw.min_elt_3 H). Qed.

  Lemma max_elt_1 : max_elt s = Some x -> In x s.
  Proof. exact (fun H => Raw.max_elt_1 H). Qed.
  Lemma max_elt_2 : max_elt s = Some x -> In y s -> ~ E.lt x y.
  Proof. exact (fun H => Raw.max_elt_2 s.(sorted) H). Qed.
  Lemma max_elt_3 : max_elt s = None -> Empty s.
  Proof. exact (fun H => Raw.max_elt_3 H). Qed.

  Lemma choose_1 : choose s = Some x -> In x s.
  Proof. exact (fun H => Raw.choose_1 H). Qed.
  Lemma choose_2 : choose s = None -> Empty s.
  Proof. exact (fun H => Raw.choose_2 H). Qed.
  Lemma choose_3 : choose s = Some x -> choose s' = Some y ->
   Equal s s' -> E.eq x y.
  Proof. exact (@Raw.choose_3 _ _ s.(sorted) s'.(sorted) x y). Qed.

  Lemma eq_refl : eq s s.
  Proof. exact (Raw.eq_refl s). Qed.
  Lemma eq_sym : eq s s' -> eq s' s.
  Proof. exact (@Raw.eq_sym s s'). Qed.
  Lemma eq_trans : eq s s' -> eq s' s'' -> eq s s''.
  Proof. exact (@Raw.eq_trans s s' s''). Qed.

  Lemma lt_trans : lt s s' -> lt s' s'' -> lt s s''.
  Proof. exact (@Raw.lt_trans s s' s''). Qed.
  Lemma lt_not_eq : lt s s' -> ~ eq s s'.
  Proof. exact (Raw.lt_not_eq s.(sorted) s'.(sorted)). Qed.

  Definition compare : Compare lt eq s s'.
  Proof.
  elim (Raw.compare s.(sorted) s'.(sorted));
   [ constructor 1 | constructor 2 | constructor 3 ];
   auto.
  Defined.

  Definition eq_dec : { eq s s' } + { ~ eq s s' }.
  Proof.
  change eq with Equal.
  case_eq (equal s s'); intro H; [left | right].
  apply equal_2; auto.
  intro H'; rewrite equal_1 in H; auto; discriminate.
  Defined.

 End Spec.

End Make.

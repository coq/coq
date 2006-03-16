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
 
  Module E := X.
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
        | Lt _ => false
        | Eq _ => true
        | Gt _ => mem x l
        end
    end.

  Fixpoint add (x : elt) (s : t) {struct s} : t :=
    match s with
    | nil => x :: nil
    | y :: l =>
        match X.compare x y with
        | Lt _ => x :: s
        | Eq _ => s
        | Gt _ => y :: add x l
        end
    end.

  Definition singleton (x : elt) : t := x :: nil. 

  Fixpoint remove (x : elt) (s : t) {struct s} : t :=
    match s with
    | nil => nil
    | y :: l =>
        match X.compare x y with
        | Lt _ => s
        | Eq _ => l
        | Gt _ => y :: remove x l
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
               | Lt _ => x :: union l s'
               | Eq _ => x :: union l l'
               | Gt _ => x' :: union_aux l'
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
               | Lt _ => inter l s'
               | Eq _ => x :: inter l l'
               | Gt _ => inter_aux l'
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
               | Lt _ => x :: diff l s'
               | Eq _ => diff l l'
               | Gt _ => diff_aux l'
               end
           end)
    end.  
   
  Fixpoint equal (s : t) : t -> bool :=
    fun s' : t =>
    match s, s' with
    | nil, nil => true
    | x :: l, x' :: l' =>
        match X.compare x x' with
        | Eq _ => equal l l'
        | _ => false
        end
    | _, _ => false
    end.

  Fixpoint subset (s s' : t) {struct s'} : bool :=
    match s, s' with
    | nil, _ => true
    | x :: l, x' :: l' =>
        match X.compare x x' with
        | Lt _ => false
        | Eq _ => subset l l'
        | Gt _ => subset s l'
        end
    | _, _ => false
    end.

  Fixpoint fold (B : Set) (f : elt -> B -> B) (s : t) {struct s} : 
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

  Lemma fold_1 :
   forall (s : t) (Hs : Sort s) (A : Set) (i : A) (f : elt -> A -> A),
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

End Raw.

(** * Encapsulation

   Now, in order to really provide a functor implementing [S], we 
   need to encapsulate everything into a type of strictly ordered lists. *)

Module Make (X: OrderedType) <: S with Module E := X.

 Module E := X.
 Module Raw := Raw X. 

 Record slist : Set :=  {this :> Raw.t; sorted : sort X.lt this}.
 Definition t := slist. 
 Definition elt := X.t.
 
 Definition In (x : elt) (s : t) := InA X.eq x s.(this).
 Definition Equal s s' := forall a : elt, In a s <-> In a s'.
 Definition Subset s s' := forall a : elt, In a s -> In a s'.
 Definition Empty s := forall a : elt, ~ In a s.
 Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
 Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.
  
 Definition In_1 (s : t) := Raw.MX.In_eq (l:=s.(this)).
 
 Definition mem (x : elt) (s : t) := Raw.mem x s.
 Definition mem_1 (s : t) := Raw.mem_1 (sorted s). 
 Definition mem_2 (s : t) := Raw.mem_2 (s:=s).

 Definition add x s := Build_slist (Raw.add_sort (sorted s) x).
 Definition add_1 (s : t) := Raw.add_1 (sorted s).
 Definition add_2 (s : t) := Raw.add_2 (sorted s).
 Definition add_3 (s : t) := Raw.add_3 (sorted s).

 Definition remove x s := Build_slist (Raw.remove_sort (sorted s) x).
 Definition remove_1 (s : t) := Raw.remove_1 (sorted s).
 Definition remove_2 (s : t) := Raw.remove_2 (sorted s).
 Definition remove_3 (s : t) := Raw.remove_3 (sorted s).
 
 Definition singleton x := Build_slist (Raw.singleton_sort x).
 Definition singleton_1 := Raw.singleton_1.
 Definition singleton_2 := Raw.singleton_2.
  
 Definition union (s s' : t) :=
   Build_slist (Raw.union_sort (sorted s) (sorted s')). 
 Definition union_1 (s s' : t) := Raw.union_1 (sorted s) (sorted s').
 Definition union_2 (s s' : t) := Raw.union_2 (sorted s) (sorted s').
 Definition union_3 (s s' : t) := Raw.union_3 (sorted s) (sorted s').

 Definition inter (s s' : t) :=
   Build_slist (Raw.inter_sort (sorted s) (sorted s')). 
 Definition inter_1 (s s' : t) := Raw.inter_1 (sorted s) (sorted s').
 Definition inter_2 (s s' : t) := Raw.inter_2 (sorted s) (sorted s').
 Definition inter_3 (s s' : t) := Raw.inter_3 (sorted s) (sorted s').
 
 Definition diff (s s' : t) :=
   Build_slist (Raw.diff_sort (sorted s) (sorted s')). 
 Definition diff_1 (s s' : t) := Raw.diff_1 (sorted s) (sorted s').
 Definition diff_2 (s s' : t) := Raw.diff_2 (sorted s) (sorted s').
 Definition diff_3 (s s' : t) := Raw.diff_3 (sorted s) (sorted s').
 
 Definition equal (s s' : t) := Raw.equal s s'. 
 Definition equal_1 (s s' : t) := Raw.equal_1 (sorted s) (sorted s').  
 Definition equal_2 (s s' : t) := Raw.equal_2 (s:=s) (s':=s').
 
 Definition subset (s s' : t) := Raw.subset s s'.
 Definition subset_1 (s s' : t) := Raw.subset_1 (sorted s) (sorted s').  
 Definition subset_2 (s s' : t) := Raw.subset_2 (s:=s) (s':=s').

 Definition empty := Build_slist Raw.empty_sort.
 Definition empty_1 := Raw.empty_1.
 
 Definition is_empty (s : t) := Raw.is_empty s.
 Definition is_empty_1 (s : t) := Raw.is_empty_1 (s:=s).
 Definition is_empty_2 (s : t) := Raw.is_empty_2 (s:=s).

 Definition elements (s : t) := Raw.elements s.
 Definition elements_1 (s : t) := Raw.elements_1 (s:=s).
 Definition elements_2 (s : t) := Raw.elements_2 (s:=s).
 Definition elements_3 (s : t) := Raw.elements_3 (sorted s).
 
 Definition min_elt (s : t) := Raw.min_elt s.
 Definition min_elt_1 (s : t) := Raw.min_elt_1 (s:=s).
 Definition min_elt_2 (s : t) := Raw.min_elt_2 (sorted s).
 Definition min_elt_3 (s : t) := Raw.min_elt_3 (s:=s).

 Definition max_elt (s : t) := Raw.max_elt s.
 Definition max_elt_1 (s : t) := Raw.max_elt_1 (s:=s).
 Definition max_elt_2 (s : t) := Raw.max_elt_2 (sorted s).
 Definition max_elt_3 (s : t) := Raw.max_elt_3 (s:=s).
  
 Definition choose := min_elt.
 Definition choose_1 := min_elt_1.
 Definition choose_2 := min_elt_3.
 
 Definition fold (B : Set) (f : elt -> B -> B) (s : t) := Raw.fold (B:=B) f s. 
 Definition fold_1 (s : t) := Raw.fold_1 (sorted s). 
 
 Definition cardinal (s : t) := Raw.cardinal s.
 Definition cardinal_1 (s : t) := Raw.cardinal_1 (sorted s). 
 
 Definition filter (f : elt -> bool) (s : t) :=
   Build_slist (Raw.filter_sort (sorted s) f).
 Definition filter_1 (s : t) := Raw.filter_1 (s:=s).
 Definition filter_2 (s : t) := Raw.filter_2 (s:=s).
 Definition filter_3 (s : t) := Raw.filter_3 (s:=s).
 
 Definition for_all (f : elt -> bool) (s : t) := Raw.for_all f s.
 Definition for_all_1 (s : t) := Raw.for_all_1 (s:=s). 
 Definition for_all_2 (s : t) := Raw.for_all_2 (s:=s). 

 Definition exists_ (f : elt -> bool) (s : t) := Raw.exists_ f s.
 Definition exists_1 (s : t) := Raw.exists_1 (s:=s). 
 Definition exists_2 (s : t) := Raw.exists_2 (s:=s). 

 Definition partition (f : elt -> bool) (s : t) :=
   let p := Raw.partition f s in
   (Build_slist (this:=fst p) (Raw.partition_sort_1 (sorted s) f),
   Build_slist (this:=snd p) (Raw.partition_sort_2 (sorted s) f)).
 Definition partition_1 (s : t) := Raw.partition_1 s.
 Definition partition_2 (s : t) := Raw.partition_2 s. 

 Definition eq (s s' : t) := Raw.eq s s'.
 Definition eq_refl (s : t) := Raw.eq_refl s.
 Definition eq_sym (s s' : t) := Raw.eq_sym (s:=s) (s':=s').
 Definition eq_trans (s s' s'' : t) :=
   Raw.eq_trans (s:=s) (s':=s') (s'':=s'').
  
 Definition lt (s s' : t) := Raw.lt s s'.
 Definition lt_trans (s s' s'' : t) :=
   Raw.lt_trans (s:=s) (s':=s') (s'':=s'').
 Definition lt_not_eq (s s' : t) := Raw.lt_not_eq (sorted s) (sorted s').

 Definition compare : forall s s' : t, Compare lt eq s s'.
 Proof.
 intros; elim (Raw.compare (sorted s) (sorted s'));
  [ constructor 1 | constructor 2 | constructor 3 ]; 
  auto. 
 Defined.

End Make.

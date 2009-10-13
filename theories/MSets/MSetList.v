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
    interface [MSetInterface.S] using strictly ordered list. *)

Require Export MSetInterface.
Set Implicit Arguments.
Unset Strict Implicit.

(** * Functions over lists

   First, we provide sets as lists which are not necessarily sorted.
   The specs are proved under the additional condition of being sorted.
   And the functions returning sets are proved to preserve this invariant. *)

Module Ops (X:OrderedType) <: WOps X.

  Definition elt := X.t.
  Definition t := list elt.

  Definition empty : t := nil.

  Definition is_empty (l : t) := if l then true else false.

  (** ** The set operations. *)

  Fixpoint mem x s :=
    match s with
    | nil => false
    | y :: l =>
        match X.compare x y with
        | Lt => false
        | Eq => true
        | Gt => mem x l
        end
    end.

  Fixpoint add x s :=
    match s with
    | nil => x :: nil
    | y :: l =>
        match X.compare x y with
        | Lt => x :: s
        | Eq => s
        | Gt => y :: add x l
        end
    end.

  Definition singleton (x : elt) := x :: nil.

  Fixpoint remove x s :=
    match s with
    | nil => nil
    | y :: l =>
        match X.compare x y with
        | Lt => s
        | Eq => l
        | Gt => y :: remove x l
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
               | Lt => x :: union l s'
               | Eq => x :: union l l'
               | Gt => x' :: union_aux l'
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
               | Lt => inter l s'
               | Eq => x :: inter l l'
               | Gt => inter_aux l'
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
               | Lt => x :: diff l s'
               | Eq => diff l l'
               | Gt => diff_aux l'
               end
           end)
    end.

  Fixpoint equal (s : t) : t -> bool :=
    fun s' : t =>
    match s, s' with
    | nil, nil => true
    | x :: l, x' :: l' =>
        match X.compare x x' with
        | Eq => equal l l'
        | _ => false
        end
    | _, _ => false
    end.

  Fixpoint subset s s' :=
    match s, s' with
    | nil, _ => true
    | x :: l, x' :: l' =>
        match X.compare x x' with
        | Lt => false
        | Eq => subset l l'
        | Gt => subset s l'
        end
    | _, _ => false
    end.

  Definition fold (B : Type) (f : elt -> B -> B) (s : t) (i : B) : B :=
    fold_left (flip f) s i.

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

  Fixpoint compare s s' :=
   match s, s' with
    | nil, nil => Eq
    | nil, _ => Lt
    | _, nil => Gt
    | x::s, x'::s' =>
      match X.compare x x' with
       | Eq => compare s s'
       | Lt => Lt
       | Gt => Gt
      end
   end.

End Ops.

Module MakeRaw (X: OrderedType) <: RawSets X.
  Module Import MX := OrderedTypeFacts X.

  Include Ops X.

  (** ** Proofs of set operation specifications. *)

  Section ForNotations.

  Notation Sort := (sort X.lt).
  Notation Inf := (lelistA X.lt).
  Notation In := (InA X.eq).

  Definition IsOk := Sort.

  Class Ok (s:t) : Prop := { ok : Sort s }.

  Hint Resolve @ok.
  Hint Constructors Ok.

  Instance Sort_Ok `(Hs : Sort s) : Ok s := Hs.

  Ltac inv_ok := match goal with
   | H:Ok (_ :: _) |- _ => apply @ok in H; inversion_clear H; inv_ok
   | H:Ok nil |- _ => clear H; inv_ok
   | H:Sort ?l |- _ => generalize (Build_Ok H); clear H; intro H; inv_ok
   | _ => idtac
  end.

  Ltac inv := invlist InA; inv_ok; invlist lelistA.
  Ltac constructors := repeat constructor.

  Ltac sort_inf_in := match goal with
   | H:Inf ?x ?l, H':In ?y ?l |- _ =>
     cut (X.lt x y); [ intro | apply Sort_Inf_In with l; auto]
   | _ => fail
  end.

  Definition inf x l :=
   match l with
   | nil => true
   | y::_ => match X.compare x y with Lt => true | _ => false end
   end.

  Fixpoint isok l :=
   match l with
   | nil => true
   | x::l => inf x l && isok l
   end.

  Lemma inf_iff : forall x l, Inf x l <-> inf x l = true.
  Proof.
  induction l as [ | y l IH].
  simpl; split; auto.
  simpl.
  elim_compare x y; intuition; try discriminate.
  inv; order.
  inv; order.
  Qed.

  Lemma isok_iff : forall l, Ok l <-> isok l = true.
  Proof.
  induction l as [ | x l IH].
  simpl; split; auto; constructor.
  simpl.
  rewrite andb_true_iff, <- inf_iff, <- IH.
  split.
  intros; inv; auto.
  constructor; intuition.
  Qed.

  Global Instance isok_Ok `(isok s = true) : Ok s | 10.
  Proof.
  intros. apply <- isok_iff. auto.
  Qed.

  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop) (s : t) := exists x, In x s /\ P x.

  Lemma mem_spec :
   forall (s : t) (x : elt) (Hs : Ok s), mem x s = true <-> In x s.
  Proof.
  induction s; intros; inv; simpl.
  intuition. discriminate. inv.
  elim_compare x a; intros; rewrite InA_cons; intuition; try order.
  discriminate.
  sort_inf_in. order.
  rewrite <- IHs; auto.
  rewrite IHs; auto.
  Qed.

  Lemma add_inf :
   forall (s : t) (x a : elt), Inf a s -> X.lt a x -> Inf a (add x s).
  Proof.
  simple induction s; simpl.
  intuition.
  intros; elim_compare x a; intros; inv; intuition.
  Qed.
  Hint Resolve add_inf.

  Global Instance add_ok s x `(Ok s) : Ok (add x s).
  Proof.
  simple induction s; simpl.
  intuition.
  intros; elim_compare x a; intros; inv; auto.
  Qed.

  Lemma add_spec :
   forall (s : t) (x y : elt) (Hs : Ok s),
    In y (add x s) <-> X.eq y x \/ In y s.
  Proof.
  induction s; simpl; intros.
  intuition. inv; auto.
  elim_compare x a; intros; inv; rewrite !InA_cons, ?IHs; intuition.
  left; order.
  Qed.

  Lemma remove_inf :
   forall (s : t) (x a : elt) (Hs : Ok s), Inf a s -> Inf a (remove x s).
  Proof.
  induction s; simpl.
  intuition.
  intros; elim_compare x a; intros; inv; auto.
  apply Inf_lt with a; auto.
  Qed.
  Hint Resolve remove_inf.

  Global Instance remove_ok s x `(Ok s) : Ok (remove x s).
  Proof.
  induction s; simpl.
  intuition.
  intros; elim_compare x a; intros; inv; auto.
  Qed.

  Lemma remove_spec :
   forall (s : t) (x y : elt) (Hs : Ok s),
    In y (remove x s) <-> In y s /\ ~X.eq y x.
  Proof.
  induction s; simpl; intros.
  intuition; inv; auto.
  elim_compare x a; intros; inv; rewrite !InA_cons, ?IHs; intuition;
   try sort_inf_in; try order.
  Qed.

  Global Instance singleton_ok x : Ok (singleton x).
  Proof.
  unfold singleton; simpl; auto.
  Qed.

  Lemma singleton_spec : forall x y : elt, In y (singleton x) <-> X.eq y x.
  Proof.
  unfold singleton; simpl; split; intros; inv; auto.
  Qed.

  Ltac induction2 :=
    simple induction s;
     [ simpl; auto; try solve [ intros; inv ]
     | intros x l Hrec; simple induction s';
        [ simpl; auto; try solve [ intros; inv ]
        | intros x' l' Hrec'; simpl; elim_compare x x'; intros; inv; auto ]].

  Lemma union_inf :
   forall (s s' : t) (a : elt) (Hs : Ok s) (Hs' : Ok s'),
   Inf a s -> Inf a s' -> Inf a (union s s').
  Proof.
  induction2.
  Qed.
  Hint Resolve union_inf.

  Global Instance union_ok s s' `(Ok s, Ok s') : Ok (union s s').
  Proof.
  induction2; constructors; try apply @ok; auto.
  apply Inf_eq with x'; auto; apply union_inf; auto; apply Inf_eq with x; auto.
  change (Inf x' (union (x :: l) l')); auto.
  Qed.

  Lemma union_spec :
   forall (s s' : t) (x : elt) (Hs : Ok s) (Hs' : Ok s'),
   In x (union s s') <-> In x s \/ In x s'.
  Proof.
  induction2; try rewrite ?InA_cons, ?Hrec, ?Hrec'; intuition; inv; auto.
  left; order.
  Qed.

  Lemma inter_inf :
   forall (s s' : t) (a : elt) (Hs : Ok s) (Hs' : Ok s'),
   Inf a s -> Inf a s' -> Inf a (inter s s').
  Proof.
  induction2.
  apply Inf_lt with x; auto.
  apply Hrec'; auto.
  apply Inf_lt with x'; auto.
  Qed.
  Hint Resolve inter_inf.

  Global Instance inter_ok s s' `(Ok s, Ok s') : Ok (inter s s').
  Proof.
  induction2.
  constructors; auto.
  apply Inf_eq with x'; auto; apply inter_inf; auto; apply Inf_eq with x; auto.
  Qed.

  Lemma inter_spec :
   forall (s s' : t) (x : elt) (Hs : Ok s) (Hs' : Ok s'),
   In x (inter s s') <-> In x s /\ In x s'.
  Proof.
  induction2; try rewrite ?InA_cons, ?Hrec, ?Hrec'; intuition; inv; auto;
   try sort_inf_in; try order.
  Qed.

  Lemma diff_inf :
   forall (s s' : t) (Hs : Ok s) (Hs' : Ok s') (a : elt),
   Inf a s -> Inf a s' -> Inf a (diff s s').
  Proof.
  induction2.
  apply Hrec; trivial.
  apply Inf_lt with x; auto.
  apply Inf_lt with x'; auto.
  apply Hrec'; auto.
  apply Inf_lt with x'; auto.
  Qed.
  Hint Resolve diff_inf.

  Global Instance diff_ok s s' `(Ok s, Ok s') : Ok (diff s s').
  Proof.
  induction2. constructors; auto. apply @ok; auto.
  Qed.

  Lemma diff_spec :
   forall (s s' : t) (x : elt) (Hs : Ok s) (Hs' : Ok s'),
   In x (diff s s') <-> In x s /\ ~In x s'.
  Proof.
  induction2; try rewrite ?InA_cons, ?Hrec, ?Hrec'; intuition; inv; auto;
   try sort_inf_in; try order.
  right; intuition; inv; order.
  Qed.

  Lemma equal_spec :
   forall (s s' : t) (Hs : Ok s) (Hs' : Ok s'),
   equal s s' = true <-> Equal s s'.
  Proof.
  induction s as [ | x s IH]; intros [ | x' s'] Hs Hs'; simpl.
  intuition.
  split; intros H. discriminate. assert (In x' nil) by (rewrite H; auto). inv.
  split; intros H. discriminate. assert (In x nil) by (rewrite <-H; auto). inv.
  inv.
  elim_compare x x'; intros C; try discriminate.
  (* x=x' *)
  rewrite IH; auto.
  split; intros E y; specialize (E y).
  rewrite !InA_cons, E, C; intuition.
  rewrite !InA_cons, C in E. intuition; try sort_inf_in; order.
  (* x<x' *)
  split; intros E. discriminate.
  assert (In x (x'::s')) by (rewrite <- E; auto).
  inv; try sort_inf_in; order.
  (* x>x' *)
  split; intros E. discriminate.
  assert (In x' (x::s)) by (rewrite E; auto).
  inv; try sort_inf_in; order.
  Qed.

  Lemma subset_spec :
   forall (s s' : t) (Hs : Ok s) (Hs' : Ok s'),
   subset s s' = true <-> Subset s s'.
  Proof.
  intros s s'; revert s.
  induction s' as [ | x' s' IH]; intros [ | x s] Hs Hs'; simpl; auto.
  split; try red; intros; auto.
  split; intros H. discriminate. assert (In x nil) by (apply H; auto). inv.
  split; try red; intros; auto. inv.
  inv. elim_compare x x'; intros C.
  (* x=x' *)
  rewrite IH; auto.
  split; intros S y; specialize (S y).
  rewrite !InA_cons, C. intuition.
  rewrite !InA_cons, C in S. intuition; try sort_inf_in; order.
  (* x<x' *)
  split; intros S. discriminate.
  assert (In x (x'::s')) by (apply S; auto).
  inv; try sort_inf_in; order.
  (* x>x' *)
  rewrite IH; auto.
  split; intros S y; specialize (S y).
  rewrite !InA_cons. intuition.
  rewrite !InA_cons in S. rewrite !InA_cons. intuition; try sort_inf_in; order.
  Qed.

  Global Instance empty_ok : Ok empty.
  Proof.
  constructors.
  Qed.

  Lemma empty_spec : Empty empty.
  Proof.
  unfold Empty, empty; intuition; inv.
  Qed.

  Lemma is_empty_spec : forall s : t, is_empty s = true <-> Empty s.
  Proof.
  intros [ | x s]; simpl.
  split; auto. intros _ x H. inv.
  split. discriminate. intros H. elim (H x); auto.
  Qed.

  Lemma elements_spec1 : forall (s : t) (x : elt), In x (elements s) <-> In x s.
  Proof.
  intuition.
  Qed.

  Lemma elements_spec2 : forall (s : t) (Hs : Ok s), Sort (elements s).
  Proof.
  auto.
  Qed.

  Lemma elements_spec2w : forall (s : t) (Hs : Ok s), NoDupA X.eq (elements s).
  Proof.
  auto.
  Qed.

  Lemma min_elt_spec1 : forall (s : t) (x : elt), min_elt s = Some x -> In x s.
  Proof.
  destruct s; simpl; inversion 1; auto.
  Qed.

  Lemma min_elt_spec2 :
   forall (s : t) (x y : elt) (Hs : Ok s),
   min_elt s = Some x -> In y s -> ~ X.lt y x.
  Proof.
  induction s as [ | x s IH]; simpl; inversion 2; subst.
  intros; inv; try sort_inf_in; order.
  Qed.

  Lemma min_elt_spec3 : forall s : t, min_elt s = None -> Empty s.
  Proof.
  destruct s; simpl; red; intuition. inv. discriminate.
  Qed.

  Lemma max_elt_spec1 : forall (s : t) (x : elt), max_elt s = Some x -> In x s.
  Proof.
  induction s as [ | x s IH]. inversion 1.
  destruct s as [ | y s]. simpl. inversion 1; subst; auto.
  right; apply IH; auto.
  Qed.

  Lemma max_elt_spec2 :
   forall (s : t) (x y : elt) (Hs : Ok s),
   max_elt s = Some x -> In y s -> ~ X.lt x y.
  Proof.
  induction s as [ | a s IH]. inversion 2.
  destruct s as [ | b s]. inversion 2; subst. intros; inv; order.
  intros. inv; auto.
  assert (~X.lt x b) by (apply IH; auto).
  assert (X.lt a b) by auto.
  order.
  Qed.

  Lemma max_elt_spec3 : forall s : t, max_elt s = None -> Empty s.
  Proof.
  induction s as [ | a s IH]. red; intuition; inv.
  destruct s as [ | b s]. inversion 1.
  intros; elim IH with b; auto.
  Qed.

  Definition choose_spec1 :
    forall (s : t) (x : elt), choose s = Some x -> In x s := min_elt_spec1.

  Definition choose_spec2 :
    forall s : t, choose s = None -> Empty s := min_elt_spec3.

  Lemma choose_spec3: forall s s' x x', Ok s -> Ok s' ->
   choose s = Some x -> choose s' = Some x' -> Equal s s' -> X.eq x x'.
  Proof.
   unfold choose; intros s s' x x' Hs Hs' Hx Hx' H.
   assert (~X.lt x x').
    apply min_elt_spec2 with s'; auto.
    rewrite <-H; auto using min_elt_spec1.
   assert (~X.lt x' x).
    apply min_elt_spec2 with s; auto.
    rewrite H; auto using min_elt_spec1.
   order.
  Qed.

  Lemma fold_spec :
   forall (s : t) (A : Type) (i : A) (f : elt -> A -> A),
   fold f s i = fold_left (flip f) (elements s) i.
  Proof.
  reflexivity.
  Qed.

  Lemma cardinal_spec :
   forall (s : t) (Hs : Ok s),
   cardinal s = length (elements s).
  Proof.
  auto.
  Qed.

  Lemma filter_inf :
   forall (s : t) (x : elt) (f : elt -> bool) (Hs : Ok s),
   Inf x s -> Inf x (filter f s).
  Proof.
  simple induction s; simpl.
  intuition.
  intros x l Hrec a f Hs Ha; inv.
  case (f x); auto.
  apply Hrec; auto.
  apply Inf_lt with x; auto.
  Qed.

  Global Instance filter_ok s f `(Ok s) : Ok (filter f s).
  Proof.
  simple induction s; simpl.
  auto.
  intros x l Hrec f Hs; inv.
  case (f x); auto.
  constructors; auto.
  apply filter_inf; auto.
  Qed.

  Lemma filter_spec :
   forall (s : t) (x : elt) (f : elt -> bool),
   Proper (X.eq==>eq) f ->
   (In x (filter f s) <-> In x s /\ f x = true).
  Proof.
  induction s; simpl; intros.
  split; intuition; inv.
  destruct (f a) as [ ]_eqn:F; rewrite !InA_cons, ?IHs; intuition.
  setoid_replace x with a; auto.
  setoid_replace a with x in F; auto; congruence.
  Qed.

  Lemma for_all_spec :
   forall (s : t) (f : elt -> bool),
   Proper (X.eq==>eq) f ->
   (for_all f s = true <-> For_all (fun x => f x = true) s).
  Proof.
  unfold For_all; induction s; simpl; intros.
  split; intros; auto. inv.
  destruct (f a) as [ ]_eqn:F.
  rewrite IHs; auto. firstorder. inv; auto.
  setoid_replace x with a; auto.
  split; intros H'. discriminate.
  rewrite H' in F; auto.
  Qed.

  Lemma exists_spec :
   forall (s : t) (f : elt -> bool),
   Proper (X.eq==>eq) f ->
   (exists_ f s = true <-> Exists (fun x => f x = true) s).
  Proof.
  unfold Exists; induction s; simpl; intros.
  firstorder. discriminate. inv.
  destruct (f a) as [ ]_eqn:F.
  firstorder.
  rewrite IHs; auto.
  firstorder.
  inv.
  setoid_replace a with x in F; auto; congruence.
  exists x; auto.
  Qed.

  Lemma partition_inf1 :
   forall (s : t) (f : elt -> bool) (x : elt) (Hs : Ok s),
   Inf x s -> Inf x (fst (partition f s)).
  Proof.
  simple induction s; simpl.
  intuition.
  intros x l Hrec f a Hs Ha; inv.
  generalize (Hrec f a H).
  case (f x); case (partition f l); simpl.
  auto.
  intros; apply H2; apply Inf_lt with x; auto.
  Qed.

  Lemma partition_inf2 :
   forall (s : t) (f : elt -> bool) (x : elt) (Hs : Ok s),
   Inf x s -> Inf x (snd (partition f s)).
  Proof.
  simple induction s; simpl.
  intuition.
  intros x l Hrec f a Hs Ha; inv.
  generalize (Hrec f a H).
  case (f x); case (partition f l); simpl.
  intros; apply H2; apply Inf_lt with x; auto.
  auto.
  Qed.

  Global Instance partition_ok1 s f `(Ok s) : Ok (fst (partition f s)).
  Proof.
  simple induction s; simpl.
  auto.
  intros x l Hrec f Hs; inv.
  generalize (Hrec f H); generalize (@partition_inf1 l f x).
  case (f x); case (partition f l); simpl; auto.
  Qed.

  Global Instance partition_ok2 s f `(Ok s) : Ok (snd (partition f s)).
  Proof.
  simple induction s; simpl.
  auto.
  intros x l Hrec f Hs; inv.
  generalize (Hrec f H); generalize (@partition_inf2 l f x).
  case (f x); case (partition f l); simpl; auto.
  Qed.

  Lemma partition_spec1 :
   forall (s : t) (f : elt -> bool),
   Proper (X.eq==>eq) f -> Equal (fst (partition f s)) (filter f s).
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

  Lemma partition_spec2 :
   forall (s : t) (f : elt -> bool),
   Proper (X.eq==>eq) f ->
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

  End ForNotations.

  Definition In := InA X.eq.
  Instance In_compat : Proper (X.eq==>eq==> iff) In.
  Proof. repeat red; intros; rewrite H, H0; auto. Qed.

(*
  Module IN <: IN X.
   Definition t := t.
   Definition In := In.
   Instance In_compat : Proper (X.eq==>eq==>iff) In.
   Proof.
   intros x x' Ex s s' Es. subst. rewrite Ex; intuition.
   Qed.
   Definition Equal := Equal.
   Definition Empty := Empty.
  End IN.
  Include MakeSetOrdering X IN.

  Lemma Ok_Above_Add : forall x s, Ok (x::s) -> Above x s /\ Add x s (x::s).
  Proof.
  intros.
  inver Ok.
  split.
  intros y Hy. eapply Sort_Inf_In; eauto.
  red. intuition. inver In; auto. rewrite <- H2; left; auto.
  right; auto.
  Qed.

  Lemma compare_spec :
   forall (s s' : t) (Hs : Ok s) (Hs' : Ok s'), Cmp eq lt (compare s s') s s'.
  Proof.
  induction s as [|x s IH]; intros [|x' s'] Hs Hs'; simpl; intuition.
  destruct (Ok_Above_Add Hs').
  eapply lt_empty_l; eauto. intros y Hy. inver InA.
  destruct (Ok_Above_Add Hs).
  eapply lt_empty_l; eauto. intros y Hy. inver InA.
  destruct (Ok_Above_Add Hs); destruct (Ok_Above_Add Hs').
  inver Ok. unfold Ok in IH. specialize (IH s').
  elim_compare x x'; intros.
  destruct (compare s s'); unfold Cmp, flip in IH; auto.
  intro y; split; intros; inver InA; try (left; order).
  right; rewrite <- IH; auto.
  right; rewrite IH; auto.
  eapply (@lt_add_eq x x'); eauto.
  eapply (@lt_add_eq x' x); eauto.
  eapply (@lt_add_lt x x'); eauto.
  eapply (@lt_add_lt x' x); eauto.
  Qed.
*)

  Module L := MakeListOrdering X.
  Definition eq := L.eq.
  Definition eq_equiv := L.eq_equiv.
  Definition lt l1 l2 :=
    exists l1', exists l2', Ok l1' /\ Ok l2' /\
      eq l1 l1' /\ eq l2 l2' /\ L.lt l1' l2'.

  Instance lt_strorder : StrictOrder lt.
  Proof.
  split.
  intros s (s1 & s2 & B1 & B2 & E1 & E2 & L).
  assert (eqlistA X.eq s1 s2).
   apply SortA_equivlistA_eqlistA with (ltA:=X.lt); auto using @ok with *.
   transitivity s; auto. symmetry; auto.
  rewrite H in L.
  apply (StrictOrder_Irreflexive s2); auto.
  intros s1 s2 s3 (s1' & s2' & B1 & B2 & E1 & E2 & L12)
                  (s2'' & s3' & B2' & B3 & E2' & E3 & L23).
  exists s1', s3'; do 4 (split; trivial).
  assert (eqlistA X.eq s2' s2'').
   apply SortA_equivlistA_eqlistA with (ltA:=X.lt); auto using @ok with *.
   transitivity s2; auto. symmetry; auto.
  transitivity s2'; auto.
  rewrite H; auto.
  Qed.

  Instance lt_compat : Proper (eq==>eq==>iff) lt.
  Proof.
  intros s1 s2 E12 s3 s4 E34. split.
  intros (s1' & s3' & B1 & B3 & E1 & E3 & LT).
  exists s1', s3'; do 2 (split; trivial).
   split. transitivity s1; auto. symmetry; auto.
   split; auto. transitivity s3; auto. symmetry; auto.
  intros (s1' & s3' & B1 & B3 & E1 & E3 & LT).
  exists s1', s3'; do 2 (split; trivial).
   split. transitivity s2; auto.
   split; auto. transitivity s4; auto.
  Qed.

  Lemma compare_spec_aux : forall s s', Cmp eq L.lt (compare s s') s s'.
  Proof.
  induction s as [|x s IH]; intros [|x' s']; simpl; intuition.
  red; auto.
  elim_compare x x'; intros; auto.
  specialize (IH s').
  destruct (compare s s'); unfold Cmp, flip, eq in IH; auto.
  apply L.eq_cons; auto.
  Qed.

  Lemma compare_spec : forall s s', Ok s -> Ok s' ->
   Cmp eq lt (compare s s') s s'.
  Proof.
  intros s s' Hs Hs'.
  generalize (compare_spec_aux s s').
  destruct (compare s s'); unfold Cmp, flip in *; auto.
  exists s, s'; repeat split; auto using @ok.
  exists s', s; repeat split; auto using @ok.
  Qed.

End MakeRaw.

(** * Encapsulation

   Now, in order to really provide a functor implementing [S], we
   need to encapsulate everything into a type of strictly ordered lists. *)

Module Make (X: OrderedType) <: S with Module E := X.
 Module Raw := MakeRaw X.
 Include Raw2Sets X Raw.
End Make.

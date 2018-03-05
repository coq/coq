(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * FMapPositive : an implementation of FMapInterface for [positive] keys. *)

Require Import Bool OrderedType ZArith OrderedType OrderedTypeEx FMapInterface.

Set Implicit Arguments.
Local Open Scope positive_scope.
Local Unset Elimination Schemes.

(** This file is an adaptation to the [FMap] framework of a work by
  Xavier Leroy and Sandrine Blazy (used for building certified compilers).
  Keys are of type [positive], and maps are binary trees: the sequence
  of binary digits of a positive number corresponds to a path in such a tree.
  This is quite similar to the [IntMap] library, except that no path
  compression is implemented, and that the current file is simple enough to be
  self-contained. *)

(** First, some stuff about [positive] *)

Fixpoint append (i j : positive) : positive :=
    match i with
      | xH => j
      | xI ii => xI (append ii j)
      | xO ii => xO (append ii j)
    end.

Lemma append_assoc_0 :
  forall (i j : positive), append i (xO j) = append (append i (xO xH)) j.
Proof.
 induction i; intros; destruct j; simpl;
 try rewrite (IHi (xI j));
 try rewrite (IHi (xO j));
 try rewrite <- (IHi xH);
 auto.
Qed.

Lemma append_assoc_1 :
  forall (i j : positive), append i (xI j) = append (append i (xI xH)) j.
Proof.
 induction i; intros; destruct j; simpl;
 try rewrite (IHi (xI j));
 try rewrite (IHi (xO j));
 try rewrite <- (IHi xH);
 auto.
Qed.

Lemma append_neutral_r : forall (i : positive), append i xH = i.
Proof.
 induction i; simpl; congruence.
Qed.

Lemma append_neutral_l : forall (i : positive), append xH i = i.
Proof.
 simpl; auto.
Qed.


(** The module of maps over positive keys *)

Module PositiveMap <: S with Module E:=PositiveOrderedTypeBits.

  Module E:=PositiveOrderedTypeBits.
  Module ME:=KeyOrderedType E.

  Definition key := positive : Type. 

  Inductive tree (A : Type) :=
    | Leaf : tree A
    | Node : tree A -> option A -> tree A -> tree A.

  Scheme tree_ind := Induction for tree Sort Prop.

  Definition t := tree.

  Section A.
  Variable A:Type.

  Arguments Leaf {A}.

  Definition empty : t A := Leaf.

  Fixpoint is_empty (m : t A) : bool :=
   match m with
    | Leaf => true
    | Node l None r => (is_empty l) && (is_empty r)
    | _ => false
   end.

  Fixpoint find (i : key) (m : t A) : option A :=
    match m with
    | Leaf => None
    | Node l o r =>
        match i with
        | xH => o
        | xO ii => find ii l
        | xI ii => find ii r
        end
    end.

  Fixpoint mem (i : key) (m : t A) : bool :=
    match m with
    | Leaf => false
    | Node l o r =>
        match i with
        | xH => match o with None => false | _ => true end
        | xO ii => mem ii l
        | xI ii => mem ii r
        end
    end.

  Fixpoint add (i : key) (v : A) (m : t A) : t A :=
    match m with
    | Leaf =>
        match i with
        | xH => Node Leaf (Some v) Leaf
        | xO ii => Node (add ii v Leaf) None Leaf
        | xI ii => Node Leaf None (add ii v Leaf)
        end
    | Node l o r =>
        match i with
        | xH => Node l (Some v) r
        | xO ii => Node (add ii v l) o r
        | xI ii => Node l o (add ii v r)
        end
    end.

  Fixpoint remove (i : key) (m : t A) : t A :=
    match i with
    | xH =>
        match m with
        | Leaf => Leaf
        | Node Leaf o Leaf => Leaf
        | Node l o r => Node l None r
        end
    | xO ii =>
        match m with
        | Leaf => Leaf
        | Node l None Leaf =>
            match remove ii l with
            | Leaf => Leaf
            | mm => Node mm None Leaf
            end
        | Node l o r => Node (remove ii l) o r
        end
    | xI ii =>
        match m with
        | Leaf => Leaf
        | Node Leaf None r =>
            match remove ii r with
            | Leaf => Leaf
            | mm => Node Leaf None mm
            end
        | Node l o r => Node l o (remove ii r)
        end
    end.

  (** [elements] *)

    Fixpoint xelements (m : t A) (i : key) : list (key * A) :=
      match m with
      | Leaf => nil
      | Node l None r =>
          (xelements l (append i (xO xH))) ++ (xelements r (append i (xI xH)))
      | Node l (Some x) r =>
          (xelements l (append i (xO xH)))
          ++ ((i, x) :: xelements r (append i (xI xH)))
      end.

  (* Note: function [xelements] above is inefficient.  We should apply
     deforestation to it, but that makes the proofs even harder. *)

  Definition elements (m : t A) := xelements m xH.

  (** [cardinal] *)

  Fixpoint cardinal (m : t A) : nat :=
    match m with
      | Leaf => 0%nat
      | Node l None r => (cardinal l + cardinal r)%nat
      | Node l (Some _) r => S (cardinal l + cardinal r)
    end.

  Section CompcertSpec.

  Theorem gempty:
    forall (i: key), find i empty = None.
  Proof.
    destruct i; simpl; auto.
  Qed.

  Theorem gss:
    forall (i: key) (x: A) (m: t A), find i (add i x m) = Some x.
  Proof.
    induction i; destruct m; simpl; auto.
  Qed.

  Lemma gleaf : forall (i : key), find i (Leaf : t A) = None.
  Proof. exact gempty. Qed.

  Theorem gso:
    forall (i j: key) (x: A) (m: t A),
    i <> j -> find i (add j x m) = find i m.
  Proof.
    induction i; intros; destruct j; destruct m; simpl;
       try rewrite <- (gleaf i); auto; try apply IHi; congruence.
  Qed.

  Lemma rleaf : forall (i : key), remove i Leaf = Leaf.
  Proof. destruct i; simpl; auto. Qed.

  Theorem grs:
    forall (i: key) (m: t A), find i (remove i m) = None.
  Proof.
    induction i; destruct m.
     simpl; auto.
     destruct m1; destruct o; destruct m2 as [ | ll oo rr]; simpl; auto.
      rewrite (rleaf i); auto.
      cut (find i (remove i (Node ll oo rr)) = None).
        destruct (remove i (Node ll oo rr)); auto; apply IHi.
        apply IHi.
     simpl; auto.
     destruct m1 as [ | ll oo rr]; destruct o; destruct m2; simpl; auto.
      rewrite (rleaf i); auto.
      cut (find i (remove i (Node ll oo rr)) = None).
        destruct (remove i (Node ll oo rr)); auto; apply IHi.
        apply IHi.
     simpl; auto.
     destruct m1; destruct m2; simpl; auto.
  Qed.

  Theorem gro:
    forall (i j: key) (m: t A),
    i <> j -> find i (remove j m) = find i m.
  Proof.
    induction i; intros; destruct j; destruct m;
        try rewrite (rleaf (xI j));
        try rewrite (rleaf (xO j));
        try rewrite (rleaf 1); auto;
        destruct m1; destruct o; destruct m2;
        simpl;
        try apply IHi; try congruence;
        try rewrite (rleaf j); auto;
        try rewrite (gleaf i); auto.
     cut (find i (remove j (Node m2_1 o m2_2)) = find i (Node m2_1 o m2_2));
        [ destruct (remove j (Node m2_1 o m2_2)); try rewrite (gleaf i); auto
        | apply IHi; congruence ].
     destruct (remove j (Node m1_1 o0 m1_2)); simpl; try rewrite (gleaf i);
        auto.
     destruct (remove j (Node m2_1 o m2_2)); simpl; try rewrite (gleaf i);
        auto.
     cut (find i (remove j (Node m1_1 o0 m1_2)) = find i (Node m1_1 o0 m1_2));
        [ destruct (remove j (Node m1_1 o0 m1_2)); try rewrite (gleaf i); auto
        | apply IHi; congruence ].
     destruct (remove j (Node m2_1 o m2_2)); simpl; try rewrite (gleaf i);
        auto.
     destruct (remove j (Node m1_1 o0 m1_2)); simpl; try rewrite (gleaf i);
        auto.
  Qed.

  Lemma xelements_correct:
      forall (m: t A) (i j : key) (v: A),
      find i m = Some v -> List.In (append j i, v) (xelements m j).
    Proof.
      induction m; intros.
       rewrite (gleaf i) in H; discriminate. 
       destruct o; destruct i; simpl; simpl in H.
        rewrite append_assoc_1; apply in_or_app; right; apply in_cons;
          apply IHm2; auto.
        rewrite append_assoc_0; apply in_or_app; left; apply IHm1; auto.
        rewrite append_neutral_r; apply in_or_app; injection H as ->;
          right; apply in_eq.
        rewrite append_assoc_1; apply in_or_app; right; apply IHm2; auto.
        rewrite append_assoc_0; apply in_or_app; left; apply IHm1; auto.
        congruence.
    Qed.

  Theorem elements_correct:
    forall (m: t A) (i: key) (v: A),
    find i m = Some v -> List.In (i, v) (elements m).
  Proof.
    intros m i v H.
    exact (xelements_correct m i xH H).
  Qed.

  Fixpoint xfind (i j : key) (m : t A) : option A :=
      match i, j with
      | _, xH => find i m
      | xO ii, xO jj => xfind ii jj m
      | xI ii, xI jj => xfind ii jj m
      | _, _ => None
      end.

   Lemma xfind_left :
      forall (j i : key) (m1 m2 : t A) (o : option A) (v : A),
      xfind i (append j (xO xH)) m1 = Some v -> xfind i j (Node m1 o m2) = Some v.
    Proof.
      induction j; intros; destruct i; simpl; simpl in H; auto; try congruence.
      destruct i; simpl in *; auto.
    Qed.

    Lemma xelements_ii :
      forall (m: t A) (i j : key) (v: A),
      List.In (xI i, v) (xelements m (xI j)) -> List.In (i, v) (xelements m j).
    Proof.
      induction m.
       simpl; auto.
       intros; destruct o; simpl; simpl in H; destruct (in_app_or _ _ _ H);
         apply in_or_app.
        left; apply IHm1; auto.
        right; destruct (in_inv H0).
         injection H1 as -> ->; apply in_eq.
         apply in_cons; apply IHm2; auto.
        left; apply IHm1; auto.
        right; apply IHm2; auto.
    Qed.

    Lemma xelements_io :
      forall (m: t A) (i j : key) (v: A),
      ~List.In (xI i, v) (xelements m (xO j)).
    Proof.
      induction m.
       simpl; auto.
       intros; destruct o; simpl; intro H; destruct (in_app_or _ _ _ H).
        apply (IHm1 _ _ _ H0).
        destruct (in_inv H0).
         congruence.
         apply (IHm2 _ _ _ H1).
        apply (IHm1 _ _ _ H0).
        apply (IHm2 _ _ _ H0).
    Qed.

    Lemma xelements_oo :
      forall (m: t A) (i j : key) (v: A),
      List.In (xO i, v) (xelements m (xO j)) -> List.In (i, v) (xelements m j).
    Proof.
      induction m.
       simpl; auto.
       intros; destruct o; simpl; simpl in H; destruct (in_app_or _ _ _ H);
         apply in_or_app.
        left; apply IHm1; auto.
        right; destruct (in_inv H0).
         injection H1 as -> ->; apply in_eq.
         apply in_cons; apply IHm2; auto.
        left; apply IHm1; auto.
        right; apply IHm2; auto.
    Qed.

    Lemma xelements_oi :
      forall (m: t A) (i j : key) (v: A),
      ~List.In (xO i, v) (xelements m (xI j)).
    Proof.
      induction m.
       simpl; auto.
       intros; destruct o; simpl; intro H; destruct (in_app_or _ _ _ H).
        apply (IHm1 _ _ _ H0).
        destruct (in_inv H0).
         congruence.
         apply (IHm2 _ _ _ H1).
        apply (IHm1 _ _ _ H0).
        apply (IHm2 _ _ _ H0).
    Qed.

    Lemma xelements_ih :
      forall (m1 m2: t A) (o: option A) (i : key) (v: A),
      List.In (xI i, v) (xelements (Node m1 o m2) xH) -> List.In (i, v) (xelements m2 xH).
    Proof.
      destruct o; simpl; intros; destruct (in_app_or _ _ _ H).
        absurd (List.In (xI i, v) (xelements m1 2)); auto; apply xelements_io; auto.
        destruct (in_inv H0).
         congruence.
         apply xelements_ii; auto.
        absurd (List.In (xI i, v) (xelements m1 2)); auto; apply xelements_io; auto.
        apply xelements_ii; auto.
    Qed.

    Lemma xelements_oh :
      forall (m1 m2: t A) (o: option A) (i : key) (v: A),
      List.In (xO i, v) (xelements (Node m1 o m2) xH) -> List.In (i, v) (xelements m1 xH).
    Proof.
      destruct o; simpl; intros; destruct (in_app_or _ _ _ H).
        apply xelements_oo; auto.
        destruct (in_inv H0).
         congruence.
         absurd (List.In (xO i, v) (xelements m2 3)); auto; apply xelements_oi; auto.
        apply xelements_oo; auto.
        absurd (List.In (xO i, v) (xelements m2 3)); auto; apply xelements_oi; auto.
    Qed.

    Lemma xelements_hi :
      forall (m: t A) (i : key) (v: A),
      ~List.In (xH, v) (xelements m (xI i)).
    Proof.
      induction m; intros.
       simpl; auto.
       destruct o; simpl; intro H; destruct (in_app_or _ _ _ H).
        generalize H0; apply IHm1; auto.
        destruct (in_inv H0).
         congruence.
         generalize H1; apply IHm2; auto.
        generalize H0; apply IHm1; auto.
        generalize H0; apply IHm2; auto.
    Qed.

    Lemma xelements_ho :
      forall (m: t A) (i : key) (v: A),
      ~List.In (xH, v) (xelements m (xO i)).
    Proof.
      induction m; intros.
       simpl; auto.
       destruct o; simpl; intro H; destruct (in_app_or _ _ _ H).
        generalize H0; apply IHm1; auto.
        destruct (in_inv H0).
         congruence.
         generalize H1; apply IHm2; auto.
        generalize H0; apply IHm1; auto.
        generalize H0; apply IHm2; auto.
    Qed.

    Lemma find_xfind_h :
      forall (m: t A) (i: key), find i m = xfind i xH m.
    Proof.
      destruct i; simpl; auto.
    Qed.

    Lemma xelements_complete:
      forall (i j : key) (m: t A) (v: A),
      List.In (i, v) (xelements m j) -> xfind i j m = Some v.
    Proof.
      induction i; simpl; intros; destruct j; simpl.
       apply IHi; apply xelements_ii; auto.
       absurd (List.In (xI i, v) (xelements m (xO j))); auto; apply xelements_io.
       destruct m.
        simpl in H; tauto.
        rewrite find_xfind_h. apply IHi. apply (xelements_ih _ _ _ _ _ H).
       absurd (List.In (xO i, v) (xelements m (xI j))); auto; apply xelements_oi.
       apply IHi; apply xelements_oo; auto.
       destruct m.
        simpl in H; tauto.
        rewrite find_xfind_h. apply IHi. apply (xelements_oh _ _ _ _ _ H).
       absurd (List.In (xH, v) (xelements m (xI j))); auto; apply xelements_hi.
       absurd (List.In (xH, v) (xelements m (xO j))); auto; apply xelements_ho.
       destruct m.
        simpl in H; tauto.
        destruct o; simpl in H; destruct (in_app_or _ _ _ H).
         absurd (List.In (xH, v) (xelements m1 (xO xH))); auto; apply xelements_ho.
         destruct (in_inv H0).
          congruence.
          absurd (List.In (xH, v) (xelements m2 (xI xH))); auto; apply xelements_hi.
         absurd (List.In (xH, v) (xelements m1 (xO xH))); auto; apply xelements_ho.
         absurd (List.In (xH, v) (xelements m2 (xI xH))); auto; apply xelements_hi.
    Qed.

  Theorem elements_complete:
    forall (m: t A) (i: key) (v: A),
    List.In (i, v) (elements m) -> find i m = Some v.
  Proof.
    intros m i v H.
    unfold elements in H.
    rewrite find_xfind_h.
    exact (xelements_complete i xH m v H).
  Qed.

  Lemma cardinal_1 :
   forall (m: t A), cardinal m = length (elements m).
  Proof.
   unfold elements.
   intros m; set (p:=1); clearbody p; revert m p.
   induction m; simpl; auto; intros.
   rewrite (IHm1 (append p 2)), (IHm2 (append p 3)); auto.
   destruct o; rewrite app_length; simpl; omega.
  Qed.

  End CompcertSpec.

  Definition MapsTo (i:key)(v:A)(m:t A) := find i m = Some v.

  Definition In (i:key)(m:t A) := exists e:A, MapsTo i e m.

  Definition Empty m := forall (a : key)(e:A) , ~ MapsTo a e m.

  Definition eq_key (p p':key*A) := E.eq (fst p) (fst p').

  Definition eq_key_elt (p p':key*A) :=
          E.eq (fst p) (fst p') /\ (snd p) = (snd p').

  Definition lt_key (p p':key*A) := E.lt (fst p) (fst p').

  Global Instance eqk_equiv : Equivalence eq_key := _.
  Global Instance eqke_equiv : Equivalence eq_key_elt := _.
  Global Instance ltk_strorder : StrictOrder lt_key := _.

  Lemma mem_find :
    forall m x, mem x m = match find x m with None => false | _ => true end.
  Proof.
  induction m; destruct x; simpl; auto.
  Qed.

  Lemma Empty_alt : forall m, Empty m <-> forall a, find a m = None.
  Proof.
  unfold Empty, MapsTo.
  intuition.
  generalize (H a).
  destruct (find a m); intuition.
  elim (H0 a0); auto.
  rewrite H in H0; discriminate.
  Qed.

  Lemma Empty_Node : forall l o r, Empty (Node l o r) <-> o=None /\ Empty l /\ Empty r.
  Proof.
  intros l o r.
  split.
  rewrite Empty_alt.
  split.
  destruct o; auto.
  generalize (H 1); simpl; auto.
  split; rewrite Empty_alt; intros.
  generalize (H (xO a)); auto.
  generalize (H (xI a)); auto.
  intros (H,(H0,H1)).
  subst.
  rewrite Empty_alt; intros.
  destruct a; auto.
  simpl; generalize H1; rewrite Empty_alt; auto.
  simpl; generalize H0; rewrite Empty_alt; auto.
  Qed.

  Section FMapSpec.

  Lemma mem_1 : forall m x, In x m -> mem x m = true.
  Proof.
  unfold In, MapsTo; intros m x; rewrite mem_find.
  destruct 1 as (e0,H0); rewrite H0; auto.
  Qed.

  Lemma mem_2 : forall m x, mem x m = true -> In x m.
  Proof.
  unfold In, MapsTo; intros m x; rewrite mem_find.
  destruct (find x m).
  exists a; auto.
  intros; discriminate.
  Qed.

  Variable  m m' m'' : t A.
  Variable x y z : key.
  Variable e e' : A.

  Lemma MapsTo_1 : E.eq x y -> MapsTo x e m -> MapsTo y e m.
  Proof. intros; rewrite <- H; auto. Qed.

  Lemma find_1 : MapsTo x e m -> find x m = Some e.
  Proof. unfold MapsTo; auto. Qed.

  Lemma find_2 : find x m = Some e -> MapsTo x e m.
  Proof. red; auto. Qed.

  Lemma empty_1 : Empty empty.
  Proof.
  rewrite Empty_alt; apply gempty.
  Qed.

  Lemma is_empty_1 : Empty m -> is_empty m = true.
  Proof.
  induction m; simpl; auto.
  rewrite Empty_Node.
  intros (H,(H0,H1)).
  subst; simpl.
  rewrite IHt0_1; simpl; auto.
  Qed.

  Lemma is_empty_2 : is_empty m = true -> Empty m.
  Proof.
  induction m; simpl; auto.
  rewrite Empty_alt.
  intros _; exact gempty.
  rewrite Empty_Node.
  destruct o.
  intros; discriminate.
  intro H; destruct (andb_prop _ _ H); intuition.
  Qed.

  Lemma add_1 : E.eq x y -> MapsTo y e (add x e m).
  Proof.
  unfold MapsTo.
  intro H; rewrite H; clear H.
  apply gss.
  Qed.

  Lemma add_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
  Proof.
  unfold MapsTo.
  intros; rewrite gso; auto.
  Qed.

  Lemma add_3 : ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
  Proof.
  unfold MapsTo.
  intro H; rewrite gso; auto.
  Qed.

  Lemma remove_1 : E.eq x y -> ~ In y (remove x m).
  Proof.
  intros; intro.
  generalize (mem_1 H0).
  rewrite mem_find.
  red in H.
  rewrite H.
  rewrite grs.
  intros; discriminate.
  Qed.

  Lemma remove_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
  Proof.
  unfold MapsTo.
  intro H; rewrite gro; auto.
  Qed.

  Lemma remove_3 : MapsTo y e (remove x m) -> MapsTo y e m.
  Proof.
  unfold MapsTo.
  destruct (E.eq_dec x y).
  subst.
  rewrite grs; intros; discriminate.
  rewrite gro; auto.
  Qed.

  Lemma elements_1 :
     MapsTo x e m -> InA eq_key_elt (x,e) (elements m).
  Proof.
  unfold MapsTo.
  rewrite InA_alt.
  intro H.
  exists (x,e).
  split.
  red; simpl; unfold E.eq; auto.
  apply elements_correct; auto.
  Qed.

  Lemma elements_2 :
     InA eq_key_elt (x,e) (elements m) -> MapsTo x e m.
  Proof.
  unfold MapsTo.
  rewrite InA_alt.
  intros ((e0,a),(H,H0)).
  red in H; simpl in H; unfold E.eq in H; destruct H; subst.
  apply elements_complete; auto.
  Qed.

  Lemma xelements_bits_lt_1 : forall p p0 q m v,
     List.In (p0,v) (xelements m (append p (xO q))) -> E.bits_lt p0 p.
  Proof using.
  intros.
  generalize (xelements_complete _ _ _ _ H); clear H; intros.
  revert p0 H.
  induction p; destruct p0; simpl; intros; eauto; try discriminate.
  Qed.

  Lemma xelements_bits_lt_2 : forall p p0 q m v,
     List.In (p0,v) (xelements m (append p (xI q))) -> E.bits_lt p p0.
  Proof using.
  intros.
  generalize (xelements_complete _ _ _ _ H); clear H; intros.
  revert p0 H.
  induction p; destruct p0; simpl; intros; eauto; try discriminate.
  Qed.

  Lemma xelements_sort : forall p, sort lt_key (xelements m p).
  Proof.
  induction m.
  simpl; auto.
  destruct o; simpl; intros.
  (* Some *)
  apply (SortA_app (eqA:=eq_key_elt)); auto with *.
  constructor; auto.
  apply In_InfA; intros.
  destruct y0.
  red; red; simpl.
  eapply xelements_bits_lt_2; eauto.
  intros x0 y0.
  do 2 rewrite InA_alt.
  intros (y1,(Hy1,H)) (y2,(Hy2,H0)).
  destruct y1; destruct x0; compute in Hy1; destruct Hy1; subst.
  destruct y2; destruct y0; compute in Hy2; destruct Hy2; subst.
  red; red; simpl.
  destruct H0.
  injection H0 as H0 _; subst.
  eapply xelements_bits_lt_1; eauto.
  apply E.bits_lt_trans with p.
  eapply xelements_bits_lt_1; eauto.
  eapply xelements_bits_lt_2; eauto.
  (* None *)
  apply (SortA_app (eqA:=eq_key_elt)); auto with *.
  intros x0 y0.
  do 2 rewrite InA_alt.
  intros (y1,(Hy1,H)) (y2,(Hy2,H0)).
  destruct y1; destruct x0; compute in Hy1; destruct Hy1; subst.
  destruct y2; destruct y0; compute in Hy2; destruct Hy2; subst.
  red; red; simpl.
  apply E.bits_lt_trans with p.
  eapply xelements_bits_lt_1; eauto.
  eapply xelements_bits_lt_2; eauto.
  Qed.

  Lemma elements_3 : sort lt_key (elements m).
  Proof.
  unfold elements.
  apply xelements_sort; auto.
  Qed.

  Lemma elements_3w : NoDupA eq_key (elements m).
  Proof.
    apply ME.Sort_NoDupA.
    apply elements_3.
  Qed.

  End FMapSpec.

  (** [map] and [mapi] *)

  Variable B : Type.

  Section Mapi.

    Variable f : key -> A -> B.

    Fixpoint xmapi (m : t A) (i : key) : t B :=
       match m with
        | Leaf => @Leaf B
        | Node l o r => Node (xmapi l (append i (xO xH)))
                             (option_map (f i) o)
                             (xmapi r (append i (xI xH)))
       end.

    Definition mapi m := xmapi m xH.

  End Mapi.

  Definition map (f : A -> B) m := mapi (fun _ => f) m.

  End A.

  Lemma xgmapi:
      forall (A B: Type) (f: key -> A -> B) (i j : key) (m: t A),
      find i (xmapi f m j) = option_map (f (append j i)) (find i m).
  Proof.
  induction i; intros; destruct m; simpl; auto.
  rewrite (append_assoc_1 j i); apply IHi.
  rewrite (append_assoc_0 j i); apply IHi.
  rewrite (append_neutral_r j); auto.
  Qed.

  Theorem gmapi:
    forall (A B: Type) (f: key -> A -> B) (i: key) (m: t A),
    find i (mapi f m) = option_map (f i) (find i m).
  Proof.
  intros.
  unfold mapi.
  replace (f i) with (f (append xH i)).
  apply xgmapi.
  rewrite append_neutral_l; auto.
  Qed.

  Lemma mapi_1 :
    forall (elt elt':Type)(m: t elt)(x:key)(e:elt)(f:key->elt->elt'),
    MapsTo x e m ->
    exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
  Proof.
  intros.
  exists x.
  split; [red; auto|].
  apply find_2.
  generalize (find_1 H); clear H; intros.
  rewrite gmapi.
  rewrite H.
  simpl; auto.
  Qed.

  Lemma mapi_2 :
    forall (elt elt':Type)(m: t elt)(x:key)(f:key->elt->elt'),
    In x (mapi f m) -> In x m.
  Proof.
  intros.
  apply mem_2.
  rewrite mem_find.
  destruct H as (v,H).
  generalize (find_1 H); clear H; intros.
  rewrite gmapi in H.
  destruct (find x m); auto.
  simpl in *; discriminate.
  Qed.

  Lemma map_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)(f:elt->elt'),
    MapsTo x e m -> MapsTo x (f e) (map f m).
  Proof.
  intros; unfold map.
  destruct (mapi_1 (fun _ => f) H); intuition.
  Qed.

  Lemma map_2 : forall (elt elt':Type)(m: t elt)(x:key)(f:elt->elt'),
    In x (map f m) -> In x m.
  Proof.
  intros; unfold map in *; eapply mapi_2; eauto.
  Qed.

  Section map2.
  Variable A B C : Type.
  Variable f : option A -> option B -> option C.

  Arguments Leaf {A}.

  Fixpoint xmap2_l (m : t A) : t C :=
      match m with
      | Leaf => Leaf
      | Node l o r => Node (xmap2_l l) (f o None) (xmap2_l r)
      end.

  Lemma xgmap2_l : forall (i : key) (m : t A),
          f None None = None -> find i (xmap2_l m) = f (find i m) None.
    Proof.
      induction i; intros; destruct m; simpl; auto.
    Qed.

  Fixpoint xmap2_r (m : t B) : t C :=
      match m with
      | Leaf => Leaf
      | Node l o r => Node (xmap2_r l) (f None o) (xmap2_r r)
      end.

  Lemma xgmap2_r : forall (i : key) (m : t B),
          f None None = None -> find i (xmap2_r m) = f None (find i m).
    Proof.
      induction i; intros; destruct m; simpl; auto.
    Qed.

  Fixpoint _map2 (m1 : t A)(m2 : t B) : t C :=
    match m1 with
    | Leaf => xmap2_r m2
    | Node l1 o1 r1 =>
        match m2 with
        | Leaf => xmap2_l m1
        | Node l2 o2 r2 => Node (_map2 l1 l2) (f o1 o2) (_map2 r1 r2)
        end
    end.

    Lemma gmap2: forall (i: key)(m1:t A)(m2: t B),
      f None None = None ->
      find i (_map2 m1 m2) = f (find i m1) (find i m2).
    Proof.
      induction i; intros; destruct m1; destruct m2; simpl; auto;
      try apply xgmap2_r; try apply xgmap2_l; auto.
    Qed.

  End map2.

  Definition map2 (elt elt' elt'':Type)(f:option elt->option elt'->option elt'') :=
   _map2 (fun o1 o2 => match o1,o2 with None,None => None | _, _ => f o1 o2 end).

  Lemma map2_1 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
    (x:key)(f:option elt->option elt'->option elt''),
    In x m \/ In x m' ->
    find x (map2 f m m') = f (find x m) (find x m').
  Proof.
  intros.
  unfold map2.
  rewrite gmap2; auto.
  generalize (@mem_1 _ m x) (@mem_1 _ m' x).
  do 2 rewrite mem_find.
  destruct (find x m); simpl; auto.
  destruct (find x m'); simpl; auto.
  intros.
  destruct H; intuition; try discriminate.
  Qed.

  Lemma  map2_2 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
    (x:key)(f:option elt->option elt'->option elt''),
    In x (map2 f m m') -> In x m \/ In x m'.
  Proof.
  intros.
  generalize (mem_1 H); clear H; intros.
  rewrite mem_find in H.
  unfold map2 in H.
  rewrite gmap2 in H; auto.
  generalize (@mem_2 _ m x) (@mem_2 _ m' x).
  do 2 rewrite mem_find.
  destruct (find x m); simpl in *; auto.
  destruct (find x m'); simpl in *; auto.
  Qed.


  Section Fold.

    Variables A B : Type.
    Variable f : key -> A -> B -> B.

    Fixpoint xfoldi (m : t A) (v : B) (i : key) :=
      match m with
        | Leaf _ => v
        | Node l (Some x) r =>
          xfoldi r (f i x (xfoldi l v (append i 2))) (append i 3)
        | Node l None r =>
          xfoldi r (xfoldi l v (append i 2)) (append i 3)
      end.

    Lemma xfoldi_1 :
      forall m v i,
      xfoldi m v i = fold_left (fun a p => f (fst p) (snd p) a) (xelements m i) v.
    Proof.
      set (F := fun a p => f (fst p) (snd p) a).
      induction m; intros; simpl; auto.
      destruct o.
      rewrite fold_left_app; simpl.
      rewrite <- IHm1.
      rewrite <- IHm2.
      unfold F; simpl; reflexivity.
      rewrite fold_left_app; simpl.
      rewrite <- IHm1.
      rewrite <- IHm2.
      reflexivity.
    Qed.

    Definition fold m i := xfoldi m i 1.

  End Fold.

  Lemma fold_1 :
    forall (A:Type)(m:t A)(B:Type)(i : B) (f : key -> A -> B -> B),
    fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
  Proof.
    intros; unfold fold, elements.
    rewrite xfoldi_1; reflexivity.
  Qed.

  Fixpoint equal (A:Type)(cmp : A -> A -> bool)(m1 m2 : t A) : bool :=
    match m1, m2 with
      | Leaf _, _ => is_empty m2
      | _, Leaf _ => is_empty m1
      | Node l1 o1 r1, Node l2 o2 r2 =>
           (match o1, o2 with
             | None, None => true
             | Some v1, Some v2 => cmp v1 v2
             | _, _ => false
            end)
           && equal cmp l1 l2 && equal cmp r1 r2
     end.

  Definition Equal (A:Type)(m m':t A) :=
    forall y, find y m = find y m'.
  Definition Equiv (A:Type)(eq_elt:A->A->Prop) m m' :=
    (forall k, In k m <-> In k m') /\
    (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
  Definition Equivb (A:Type)(cmp: A->A->bool) := Equiv (Cmp cmp).

  Lemma equal_1 : forall (A:Type)(m m':t A)(cmp:A->A->bool),
    Equivb cmp m m' -> equal cmp m m' = true.
  Proof.
  induction m.
  (* m = Leaf *)
  destruct 1.
  simpl.
  apply is_empty_1.
  red; red; intros.
  assert (In a (Leaf A)).
  rewrite H.
  exists e; auto.
  destruct H2; red in H2.
  destruct a; simpl in *; discriminate.
  (* m = Node *)
  destruct m'.
  (* m' = Leaf *)
  destruct 1.
  simpl.
  destruct o.
  assert (In xH (Leaf A)).
  rewrite <- H.
  exists a; red; auto.
  destruct H1; red in H1; simpl in H1; discriminate.
  apply andb_true_intro; split; apply is_empty_1; red; red; intros.
  assert (In (xO a) (Leaf A)).
  rewrite <- H.
  exists e; auto.
  destruct H2; red in H2; simpl in H2; discriminate.
  assert (In (xI a) (Leaf A)).
  rewrite <- H.
  exists e; auto.
  destruct H2; red in H2; simpl in H2; discriminate.
  (* m' = Node *)
  destruct 1.
  assert (Equivb cmp m1 m'1).
    split.
    intros k; generalize (H (xO k)); unfold In, MapsTo; simpl; auto.
    intros k e e'; generalize (H0 (xO k) e e'); unfold In, MapsTo; simpl; auto.
  assert (Equivb cmp m2 m'2).
    split.
    intros k; generalize (H (xI k)); unfold In, MapsTo; simpl; auto.
    intros k e e'; generalize (H0 (xI k) e e'); unfold In, MapsTo; simpl; auto.
  simpl.
  destruct o; destruct o0; simpl.
  repeat (apply andb_true_intro; split); auto.
  apply (H0 xH); red; auto.
  generalize (H xH); unfold In, MapsTo; simpl; intuition.
  destruct H4; try discriminate; eauto.
  generalize (H xH); unfold In, MapsTo; simpl; intuition.
  destruct H5; try discriminate; eauto.
  apply andb_true_intro; split; auto.
  Qed.

  Lemma equal_2 : forall (A:Type)(m m':t A)(cmp:A->A->bool),
    equal cmp m m' = true -> Equivb cmp m m'.
  Proof.
  induction m.
  (* m = Leaf *)
  simpl.
  split; intros.
  split.
  destruct 1; red in H0; destruct k; discriminate.
  destruct 1; elim (is_empty_2 H H0).
  red in H0; destruct k; discriminate.
  (* m = Node *)
  destruct m'.
  (* m' = Leaf *)
  simpl.
  destruct o; intros; try discriminate.
  destruct (andb_prop _ _ H); clear H.
  split; intros.
  split; unfold In, MapsTo; destruct 1.
  destruct k; simpl in *; try discriminate.
  destruct (is_empty_2 H1 (find_2 _ _ H)).
  destruct (is_empty_2 H0 (find_2 _ _ H)).
  destruct k; simpl in *; discriminate.
  unfold In, MapsTo; destruct k; simpl in *; discriminate.
  (* m' = Node *)
  destruct o; destruct o0; simpl; intros; try discriminate.
  destruct (andb_prop _ _ H); clear H.
  destruct (andb_prop _ _ H0); clear H0.
  destruct (IHm1 _ _ H2); clear H2 IHm1.
  destruct (IHm2 _ _ H1); clear H1 IHm2.
  split; intros.
  destruct k; unfold In, MapsTo in *; simpl; auto.
  split; eauto.
  destruct k; unfold In, MapsTo in *; simpl in *.
  eapply H4; eauto.
  eapply H3; eauto.
  congruence.
  destruct (andb_prop _ _ H); clear H.
  destruct (IHm1 _ _ H0); clear H0 IHm1.
  destruct (IHm2 _ _ H1); clear H1 IHm2.
  split; intros.
  destruct k; unfold In, MapsTo in *; simpl; auto.
  split; eauto.
  destruct k; unfold In, MapsTo in *; simpl in *.
  eapply H3; eauto.
  eapply H2; eauto.
  try discriminate.
  Qed.

End PositiveMap.

(** Here come some additional facts about this implementation.
  Most are facts that cannot be derivable from the general interface. *)


Module PositiveMapAdditionalFacts.
  Import PositiveMap.

  (* Derivable from the Map interface *)
  Theorem gsspec:
    forall (A:Type)(i j: key) (x: A) (m: t A),
    find i (add j x m) = if E.eq_dec i j then Some x else find i m.
  Proof.
    intros.
    destruct (E.eq_dec i j) as [ ->|]; [ apply gss | apply gso; auto ].
  Qed.

   (* Not derivable from the Map interface *)
  Theorem gsident:
    forall (A:Type)(i: key) (m: t A) (v: A),
    find i m = Some v -> add i v m = m.
  Proof.
    induction i; intros; destruct m; simpl; simpl in H; try congruence.
     rewrite (IHi m2 v H); congruence.
     rewrite (IHi m1 v H); congruence.
  Qed.

  Lemma xmap2_lr :
      forall (A B : Type)(f g: option A -> option A -> option B)(m : t A),
      (forall (i j : option A), f i j = g j i) ->
      xmap2_l f m = xmap2_r g m.
    Proof.
      induction m; intros; simpl; auto.
      rewrite IHm1; auto.
      rewrite IHm2; auto.
      rewrite H; auto.
    Qed.

  Theorem map2_commut:
    forall (A B: Type) (f g: option A -> option A -> option B),
    (forall (i j: option A), f i j = g j i) ->
    forall (m1 m2: t A),
    _map2 f m1 m2 = _map2 g m2 m1.
  Proof.
    intros A B f g Eq1.
    assert (Eq2: forall (i j: option A), g i j = f j i).
      intros; auto.
    induction m1; intros; destruct m2; simpl;
      try rewrite Eq1;
      repeat rewrite (xmap2_lr f g);
      repeat rewrite (xmap2_lr g f);
      auto.
     rewrite IHm1_1.
     rewrite IHm1_2.
     auto.
  Qed.

End PositiveMapAdditionalFacts.

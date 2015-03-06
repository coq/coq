(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(** * MMapPositive : an implementation of MMapInterface for [positive] keys. *)

Require Import Bool BinPos Orders OrdersEx OrdersLists MMapInterface.

Set Implicit Arguments.
Local Open Scope lazy_bool_scope.
Local Open Scope positive_scope.
Local Unset Elimination Schemes.

(** This file is an adaptation to the [MMap] framework of a work by
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

  Arguments Leaf {A}.

  Scheme tree_ind := Induction for tree Sort Prop.

  Definition t := tree.

  Definition empty {A} : t A := Leaf.

  Section A.
  Variable A:Type.

  Fixpoint is_empty (m : t A) : bool :=
   match m with
    | Leaf => true
    | Node l None r => (is_empty l) &&& (is_empty r)
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

  (** helper function to avoid creating empty trees that are not leaves *)

  Definition node (l : t A) (o: option A) (r : t A) : t A :=
    match o,l,r with
      | None,Leaf,Leaf => Leaf
      | _,_,_ => Node l o r
    end.

  Fixpoint remove (i : key) (m : t A) : t A :=
    match m with
    | Leaf => Leaf
    | Node l o r =>
      match i with
      | xH => node l None r
      | xO ii => node (remove ii l) o r
      | xI ii => node l o (remove ii r)
      end
    end.

  (** [bindings] *)

  Fixpoint xbindings (m : t A) (i : key) : list (key * A) :=
    match m with
      | Leaf => nil
      | Node l None r =>
          (xbindings l (append i (xO xH))) ++ (xbindings r (append i (xI xH)))
      | Node l (Some x) r =>
          (xbindings l (append i (xO xH)))
          ++ ((i, x) :: xbindings r (append i (xI xH)))
    end.

  (* Note: function [xbindings] above is inefficient.  We should apply
     deforestation to it, but that makes the proofs even harder. *)

  Definition bindings (m : t A) := xbindings m xH.

  (** [cardinal] *)

  Fixpoint cardinal (m : t A) : nat :=
    match m with
      | Leaf => 0%nat
      | Node l None r => (cardinal l + cardinal r)%nat
      | Node l (Some _) r => S (cardinal l + cardinal r)
    end.

  (** Specification proofs *)

  Lemma gleaf : forall (i : key), find i Leaf = None.
  Proof. destruct i; simpl; auto. Qed.

  Theorem empty_spec:
    forall (i: key), find i empty = None.
  Proof. exact gleaf. Qed.

  Theorem add_spec1:
    forall (m: t A) (i: key) (x: A), find i (add i x m) = Some x.
  Proof.
    intros m i; revert m.
    induction i; destruct m; simpl; auto.
  Qed.

  Theorem add_spec2:
    forall (m: t A) (i j: key) (x: A),
    i <> j -> find j (add i x m) = find j m.
  Proof.
    intros m i j; revert m i.
    induction j; destruct i, m; simpl; intros;
     rewrite ?IHj, ?gleaf; auto; try congruence.
  Qed.

  Lemma rleaf : forall (i : key), remove i Leaf = Leaf.
  Proof. destruct i; simpl; auto. Qed.

  Lemma gnode l o r i : find i (node l o r) = find i (Node l o r).
  Proof.
   destruct o,l,r; simpl; trivial.
   destruct i; simpl; now rewrite ?gleaf.
  Qed.

  Opaque node.

  Theorem remove_spec1:
    forall (m: t A)(i: key), find i (remove i m) = None.
  Proof.
    induction m; simpl.
    - intros; rewrite rleaf. apply gleaf.
    - destruct i; simpl remove; rewrite gnode; simpl; auto.
  Qed.

  Theorem remove_spec2:
    forall (m: t A)(i j: key),
    i <> j -> find j (remove i m) = find j m.
  Proof.
    induction m; simpl; intros.
    - now rewrite rleaf.
    - destruct i; simpl; rewrite gnode; destruct j; simpl; trivial;
      try apply IHm1; try apply IHm2; congruence.
  Qed.

  Lemma xbindings_correct:
      forall (m: t A) (i j : key) (v: A),
      find i m = Some v -> List.In (append j i, v) (xbindings m j).
  Proof.
    induction m; intros.
    - rewrite (gleaf i) in H; discriminate.
    - destruct o, i; simpl in *; apply in_or_app.
      + rewrite append_assoc_1. right; now apply in_cons, IHm2.
      + rewrite append_assoc_0. left; now apply IHm1.
      + rewrite append_neutral_r. injection H as ->.
        right; apply in_eq.
      + rewrite append_assoc_1. right; now apply IHm2.
      + rewrite append_assoc_0. left; now apply IHm1.
      + discriminate.
  Qed.

  Theorem bindings_correct:
    forall (m: t A) (i: key) (v: A),
    find i m = Some v -> List.In (i, v) (bindings m).
  Proof.
    intros m i v H.
    exact (xbindings_correct m i xH H).
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
      xfind i (append j (xO xH)) m1 = Some v ->
      xfind i j (Node m1 o m2) = Some v.
  Proof.
    induction j; intros; destruct i; simpl; simpl in H; auto; try congruence.
    destruct i; simpl in *; auto.
  Qed.

  Lemma xbindings_ii :
    forall (m: t A) (i j : key) (v: A),
      List.In (xI i, v) (xbindings m (xI j)) ->
      List.In (i, v) (xbindings m j).
  Proof.
    induction m.
    - simpl; auto.
    - intros; destruct o; simpl in *; rewrite in_app_iff in *;
      destruct H.
      + left; now apply IHm1.
      + right; destruct (in_inv H).
        * injection H0 as -> ->. apply in_eq.
        * apply in_cons; now apply IHm2.
      + left; now apply IHm1.
      + right; now apply IHm2.
  Qed.

  Lemma xbindings_io :
    forall (m: t A) (i j : key) (v: A),
      ~List.In (xI i, v) (xbindings m (xO j)).
  Proof.
    induction m.
    - simpl; auto.
    - intros; destruct o; simpl; intro H; destruct (in_app_or _ _ _ H).
      + apply (IHm1 _ _ _ H0).
      + destruct (in_inv H0). congruence. apply (IHm2 _ _ _ H1).
      + apply (IHm1 _ _ _ H0).
      + apply (IHm2 _ _ _ H0).
  Qed.

  Lemma xbindings_oo :
      forall (m: t A) (i j : key) (v: A),
      List.In (xO i, v) (xbindings m (xO j)) ->
      List.In (i, v) (xbindings m j).
  Proof.
    induction m.
    - simpl; auto.
    - intros; destruct o; simpl; simpl in H; destruct (in_app_or _ _ _ H);
      apply in_or_app.
      + left; now apply IHm1.
      + right; destruct (in_inv H0).
        injection H1 as -> ->; apply in_eq.
        apply in_cons; now apply IHm2.
      + left; now apply IHm1.
      + right; now apply IHm2.
  Qed.

  Lemma xbindings_oi :
    forall (m: t A) (i j : key) (v: A),
      ~List.In (xO i, v) (xbindings m (xI j)).
  Proof.
    induction m.
    - simpl; auto.
    - intros; destruct o; simpl; intro H; destruct (in_app_or _ _ _ H).
      + apply (IHm1 _ _ _ H0).
      + destruct (in_inv H0). congruence. apply (IHm2 _ _ _ H1).
      + apply (IHm1 _ _ _ H0).
      + apply (IHm2 _ _ _ H0).
  Qed.

  Lemma xbindings_ih :
      forall (m1 m2: t A) (o: option A) (i : key) (v: A),
      List.In (xI i, v) (xbindings (Node m1 o m2) xH) ->
      List.In (i, v) (xbindings m2 xH).
  Proof.
    destruct o; simpl; intros; destruct (in_app_or _ _ _ H).
    absurd (List.In (xI i, v) (xbindings m1 2)); auto; apply xbindings_io; auto.
    destruct (in_inv H0).
    congruence.
    apply xbindings_ii; auto.
    absurd (List.In (xI i, v) (xbindings m1 2)); auto; apply xbindings_io; auto.
    apply xbindings_ii; auto.
  Qed.

  Lemma xbindings_oh :
    forall (m1 m2: t A) (o: option A) (i : key) (v: A),
      List.In (xO i, v) (xbindings (Node m1 o m2) xH) ->
      List.In (i, v) (xbindings m1 xH).
  Proof.
    destruct o; simpl; intros; destruct (in_app_or _ _ _ H).
    apply xbindings_oo; auto.
    destruct (in_inv H0).
    congruence.
    absurd (List.In (xO i, v) (xbindings m2 3)); auto; apply xbindings_oi; auto.
    apply xbindings_oo; auto.
    absurd (List.In (xO i, v) (xbindings m2 3)); auto; apply xbindings_oi; auto.
  Qed.

  Lemma xbindings_hi :
      forall (m: t A) (i : key) (v: A),
      ~List.In (xH, v) (xbindings m (xI i)).
  Proof.
    induction m; intros.
    - simpl; auto.
    - destruct o; simpl; intro H; destruct (in_app_or _ _ _ H).
      + generalize H0; apply IHm1; auto.
      + destruct (in_inv H0). congruence.
        generalize H1; apply IHm2; auto.
      + generalize H0; apply IHm1; auto.
      + generalize H0; apply IHm2; auto.
  Qed.

  Lemma xbindings_ho :
    forall (m: t A) (i : key) (v: A),
      ~List.In (xH, v) (xbindings m (xO i)).
  Proof.
    induction m; intros.
    - simpl; auto.
    - destruct o; simpl; intro H; destruct (in_app_or _ _ _ H).
      + generalize H0; apply IHm1; auto.
      + destruct (in_inv H0). congruence.
        generalize H1; apply IHm2; auto.
      + generalize H0; apply IHm1; auto.
      + generalize H0; apply IHm2; auto.
  Qed.

  Lemma find_xfind_h :
    forall (m: t A) (i: key), find i m = xfind i xH m.
  Proof.
    destruct i; simpl; auto.
  Qed.

  Lemma xbindings_complete:
    forall (i j : key) (m: t A) (v: A),
      List.In (i, v) (xbindings m j) -> xfind i j m = Some v.
  Proof.
      induction i; simpl; intros; destruct j; simpl.
       apply IHi; apply xbindings_ii; auto.
       absurd (List.In (xI i, v) (xbindings m (xO j))); auto; apply xbindings_io.
       destruct m.
        simpl in H; tauto.
        rewrite find_xfind_h. apply IHi. apply (xbindings_ih _ _ _ _ _ H).
       absurd (List.In (xO i, v) (xbindings m (xI j))); auto; apply xbindings_oi.
       apply IHi; apply xbindings_oo; auto.
       destruct m.
        simpl in H; tauto.
        rewrite find_xfind_h. apply IHi. apply (xbindings_oh _ _ _ _ _ H).
       absurd (List.In (xH, v) (xbindings m (xI j))); auto; apply xbindings_hi.
       absurd (List.In (xH, v) (xbindings m (xO j))); auto; apply xbindings_ho.
       destruct m.
        simpl in H; tauto.
        destruct o; simpl in H; destruct (in_app_or _ _ _ H).
         absurd (List.In (xH, v) (xbindings m1 (xO xH))); auto; apply xbindings_ho.
         destruct (in_inv H0).
          congruence.
          absurd (List.In (xH, v) (xbindings m2 (xI xH))); auto; apply xbindings_hi.
         absurd (List.In (xH, v) (xbindings m1 (xO xH))); auto; apply xbindings_ho.
         absurd (List.In (xH, v) (xbindings m2 (xI xH))); auto; apply xbindings_hi.
  Qed.

  Theorem bindings_complete:
    forall (m: t A) (i: key) (v: A),
    List.In (i, v) (bindings m) -> find i m = Some v.
  Proof.
    intros m i v H.
    unfold bindings in H.
    rewrite find_xfind_h.
    exact (xbindings_complete i xH m v H).
  Qed.

  Lemma cardinal_spec :
   forall (m: t A), cardinal m = length (bindings m).
  Proof.
   unfold bindings.
   intros m; set (p:=1); clearbody p; revert m p.
   induction m; simpl; auto; intros.
   rewrite (IHm1 (append p 2)), (IHm2 (append p 3)); auto.
   destruct o; rewrite app_length; simpl; auto.
  Qed.

  Definition MapsTo (i:key)(v:A)(m:t A) := find i m = Some v.

  Definition In (i:key)(m:t A) := exists e:A, MapsTo i e m.

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

  Lemma mem_spec : forall m x, mem x m = true <-> In x m.
  Proof.
  unfold In, MapsTo; intros m x; rewrite mem_find.
  split.
  - destruct (find x m).
    exists a; auto.
    intros; discriminate.
  - destruct 1 as (e0,H0); rewrite H0; auto.
  Qed.

  Variable  m m' m'' : t A.
  Variable x y z : key.
  Variable e e' : A.

  Lemma MapsTo_compat : Proper (E.eq==>eq==>eq==>iff) MapsTo.
  Proof.
   intros k1 k2 Hk e1 e2 He m1 m2 Hm. red in Hk. now subst.
  Qed.

  Lemma find_spec : find x m = Some e <-> MapsTo x e m.
  Proof. reflexivity. Qed.

  Lemma is_empty_spec : is_empty m = true <-> forall k, find k m = None.
  Proof.
  induction m; simpl.
  - intuition. apply empty_spec.
  - destruct o. split; try discriminate.
    intros H. now specialize (H xH).
    rewrite <- andb_lazy_alt, andb_true_iff, IHt0_1, IHt0_2.
    clear IHt0_1 IHt0_2.
    split.
    + intros (H1,H2) k. destruct k; simpl; auto.
    + intros H; split; intros k. apply (H (xO k)). apply (H (xI k)).
  Qed.

  Lemma bindings_spec1 :
     InA eq_key_elt (x,e) (bindings m) <-> MapsTo x e m.
  Proof.
  unfold MapsTo.
  rewrite InA_alt.
  split.
  - intros ((e0,a),(H,H0)).
    red in H; simpl in H; unfold E.eq in H; destruct H; subst.
    apply bindings_complete; auto.
  - intro H.
    exists (x,e).
    split.
    red; simpl; unfold E.eq; auto.
    apply bindings_correct; auto.
  Qed.

  Lemma xbindings_bits_lt_1 : forall p p0 q m v,
     List.In (p0,v) (xbindings m (append p (xO q))) -> E.bits_lt p0 p.
  Proof.
  intros.
  generalize (xbindings_complete _ _ _ _ H); clear H; intros.
  revert p0 q m v H.
  induction p; destruct p0; simpl; intros; eauto; try discriminate.
  Qed.

  Lemma xbindings_bits_lt_2 : forall p p0 q m v,
     List.In (p0,v) (xbindings m (append p (xI q))) -> E.bits_lt p p0.
  Proof.
  intros.
  generalize (xbindings_complete _ _ _ _ H); clear H; intros.
  revert p0 q m v H.
  induction p; destruct p0; simpl; intros; eauto; try discriminate.
  Qed.

  Lemma xbindings_sort : forall p, sort lt_key (xbindings m p).
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
  eapply xbindings_bits_lt_2; eauto.
  intros x0 y0.
  do 2 rewrite InA_alt.
  intros (y1,(Hy1,H)) (y2,(Hy2,H0)).
  destruct y1; destruct x0; compute in Hy1; destruct Hy1; subst.
  destruct y2; destruct y0; compute in Hy2; destruct Hy2; subst.
  red; red; simpl.
  destruct H0.
  injection H0; clear H0; intros _ H0; subst.
  eapply xbindings_bits_lt_1; eauto.
  apply E.bits_lt_trans with p.
  eapply xbindings_bits_lt_1; eauto.
  eapply xbindings_bits_lt_2; eauto.
  (* None *)
  apply (SortA_app (eqA:=eq_key_elt)); auto with *.
  intros x0 y0.
  do 2 rewrite InA_alt.
  intros (y1,(Hy1,H)) (y2,(Hy2,H0)).
  destruct y1; destruct x0; compute in Hy1; destruct Hy1; subst.
  destruct y2; destruct y0; compute in Hy2; destruct Hy2; subst.
  red; red; simpl.
  apply E.bits_lt_trans with p.
  eapply xbindings_bits_lt_1; eauto.
  eapply xbindings_bits_lt_2; eauto.
  Qed.

  Lemma bindings_spec2 : sort lt_key (bindings m).
  Proof.
  unfold bindings.
  apply xbindings_sort; auto.
  Qed.

  Lemma bindings_spec2w : NoDupA eq_key (bindings m).
  Proof.
    apply ME.Sort_NoDupA.
    apply bindings_spec2.
  Qed.

  (** [map] and [mapi] *)

  Variable B : Type.

  Section Mapi.

    Variable f : key -> option A -> option B.

    Fixpoint xmapi (m : t A) (i : key) : t B :=
       match m with
        | Leaf => Leaf
        | Node l o r => Node (xmapi l (append i (xO xH)))
                             (f i o)
                             (xmapi r (append i (xI xH)))
       end.

  End Mapi.

  Definition mapi (f : key -> A -> B) m :=
    xmapi (fun k => option_map (f k)) m xH.

  Definition map (f : A -> B) m := mapi (fun _ => f) m.

  End A.

  Lemma xgmapi:
      forall (A B: Type) (f: key -> option A -> option B) (i j : key) (m: t A),
        (forall k, f k None = None) ->
        find i (xmapi f m j) = f (append j i) (find i m).
  Proof.
  induction i; intros; destruct m; simpl; auto.
  rewrite (append_assoc_1 j i); apply IHi; auto.
  rewrite (append_assoc_0 j i); apply IHi; auto.
  rewrite append_neutral_r; auto.
  Qed.

  Theorem mapi_spec0 :
    forall (A B: Type) (f: key -> A -> B) (i: key) (m: t A),
    find i (mapi f m) = option_map (f i) (find i m).
  Proof.
  intros.
  unfold mapi.
  replace (f i) with (f (append xH i)).
  apply xgmapi; auto.
  rewrite append_neutral_l; auto.
  Qed.

  Lemma mapi_spec :
    forall (A B: Type) (f: key -> A -> B) (m: t A) (i:key),
    exists j, E.eq j i /\
     find i (mapi f m) = option_map (f j) (find i m).
  Proof.
   intros.
   exists i. split. reflexivity. apply mapi_spec0.
  Qed.

  Lemma map_spec :
    forall (elt elt':Type)(f:elt->elt')(m: t elt)(x:key),
    find x (map f m) = option_map f (find x m).
  Proof.
  intros; unfold map. apply mapi_spec0.
  Qed.

  Section merge.
  Variable A B C : Type.
  Variable f : key -> option A -> option B -> option C.

  Fixpoint xmerge (m1 : t A)(m2 : t B)(i:positive) : t C :=
    match m1 with
    | Leaf => xmapi (fun k => f k None) m2 i
    | Node l1 o1 r1 =>
        match m2 with
        | Leaf => xmapi (fun k o => f k o None) m1 i
        | Node l2 o2 r2 =>
          Node (xmerge l1 l2 (append i (xO xH)))
               (f i o1 o2)
               (xmerge r1 r2 (append i (xI xH)))
        end
    end.

  Lemma xgmerge: forall (i j: key)(m1:t A)(m2: t B),
      (forall i, f i None None = None) ->
      find i (xmerge m1 m2 j) = f (append j i) (find i m1) (find i m2).
  Proof.
    induction i; intros; destruct m1; destruct m2; simpl; auto;
    rewrite ?xgmapi, ?IHi,
    <- ?append_assoc_1, <- ?append_assoc_0,
    ?append_neutral_l, ?append_neutral_r; auto.
  Qed.

  End merge.

  Definition merge {A B C}(f:key->option A->option B->option C) m1 m2 :=
   xmerge
     (fun k o1 o2 => match o1,o2 with
       | None,None => None
       | _, _ => f k o1 o2
      end)
     m1 m2 xH.

  Lemma merge_spec1 {A B C}(f:key->option A->option B->option C) :
    forall m m' x,
    In x m \/ In x m' ->
    exists y, E.eq y x /\
     find x (merge f m m') = f y (find x m) (find x m').
  Proof.
  intros. exists x. split. reflexivity.
  unfold merge.
  rewrite xgmerge; auto.
  rewrite append_neutral_l.
  rewrite <- 2 mem_spec, 2 mem_find in H.
  destruct (find x m); simpl; auto.
  destruct (find x m'); simpl; auto. intuition discriminate.
  Qed.

  Lemma merge_spec2 {A B C}(f:key->option A->option B->option C) :
    forall m m' x, In x (merge f m m') -> In x m \/ In x m'.
  Proof.
  intros.
  rewrite <-mem_spec, mem_find in H.
  unfold merge in H.
  rewrite xgmerge in H; auto.
  rewrite append_neutral_l in H.
  rewrite <- 2 mem_spec, 2 mem_find.
  destruct (find x m); simpl in *; auto.
  destruct (find x m'); simpl in *; auto.
  Qed.

  Section Fold.

    Variables A B : Type.
    Variable f : key -> A -> B -> B.

    Fixpoint xfoldi (m : t A) (v : B) (i : key) :=
      match m with
        | Leaf => v
        | Node l (Some x) r =>
          xfoldi r (f i x (xfoldi l v (append i 2))) (append i 3)
        | Node l None r =>
          xfoldi r (xfoldi l v (append i 2)) (append i 3)
      end.

    Lemma xfoldi_1 :
      forall m v i,
      xfoldi m v i = fold_left (fun a p => f (fst p) (snd p) a) (xbindings m i) v.
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

  Lemma fold_spec :
    forall (A:Type)(m:t A)(B:Type)(i : B) (f : key -> A -> B -> B),
    fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (bindings m) i.
  Proof.
    intros; unfold fold, bindings.
    rewrite xfoldi_1; reflexivity.
  Qed.

  Fixpoint equal (A:Type)(cmp : A -> A -> bool)(m1 m2 : t A) : bool :=
    match m1, m2 with
      | Leaf, _ => is_empty m2
      | _, Leaf => is_empty m1
      | Node l1 o1 r1, Node l2 o2 r2 =>
           (match o1, o2 with
             | None, None => true
             | Some v1, Some v2 => cmp v1 v2
             | _, _ => false
            end)
           &&& equal cmp l1 l2 &&& equal cmp r1 r2
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
  - (* m = Leaf *)
    destruct 1 as (E,_); simpl.
    apply is_empty_spec; intros k.
    destruct (find k m') eqn:F; trivial.
    assert (H : In k m') by now exists a.
    rewrite <- E in H.
    destruct H as (x,H). red in H. now rewrite gleaf in H.
  - (* m = Node *)
    destruct m'.
    + (* m' = Leaf *)
      destruct 1 as (E,_); simpl.
      destruct o.
      * assert (H : In xH (@Leaf A)).
        { rewrite <- E. now exists a. }
        destruct H as (e,H). now red in H.
      * apply andb_true_intro; split; apply is_empty_spec; intros k.
        destruct (find k m1) eqn:F; trivial.
        assert (H : In (xO k) (@Leaf A)).
        { rewrite <- E. exists a; auto. }
        destruct H as (x,H). red in H. now rewrite gleaf in H.
        destruct (find k m2) eqn:F; trivial.
        assert (H : In (xI k) (@Leaf A)).
        { rewrite <- E. exists a; auto. }
        destruct H as (x,H). red in H. now rewrite gleaf in H.
    + (* m' = Node *)
      destruct 1.
      assert (Equivb cmp m1 m'1).
      { split.
        intros k; generalize (H (xO k)); unfold In, MapsTo; simpl; auto.
        intros k e e'; generalize (H0 (xO k) e e'); unfold In, MapsTo; simpl; auto. }
      assert (Equivb cmp m2 m'2).
      { split.
        intros k; generalize (H (xI k)); unfold In, MapsTo; simpl; auto.
        intros k e e'; generalize (H0 (xI k) e e'); unfold In, MapsTo; simpl; auto. }
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
  rewrite is_empty_spec in H.
  intros (e,H'). red in H'. now rewrite H in H'.
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
  rewrite is_empty_spec in H1.
  now rewrite H1 in H.
  rewrite is_empty_spec in H0.
  now rewrite H0 in H.
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

Lemma equal_spec : forall (A:Type)(m m':t A)(cmp:A->A->bool),
    equal cmp m m' = true <-> Equivb cmp m m'.
Proof.
 split. apply equal_2. apply equal_1.
Qed.

End PositiveMap.

(** Here come some additionnal facts about this implementation.
  Most are facts that cannot be derivable from the general interface. *)

Module PositiveMapAdditionalFacts.
  Import PositiveMap.

  (* Derivable from the Map interface *)
  Theorem gsspec {A} i j x (m: t A) :
    find i (add j x m) = if E.eq_dec i j then Some x else find i m.
  Proof.
    destruct (E.eq_dec i j) as [->|];
    [ apply add_spec1 | apply add_spec2; auto ].
  Qed.

   (* Not derivable from the Map interface *)
  Theorem gsident {A} i (m:t A) v :
    find i m = Some v -> add i v m = m.
  Proof.
    revert m.
    induction i; destruct m; simpl in *; try congruence.
    - intro H; now rewrite (IHi m2 H).
    - intro H; now rewrite (IHi m1 H).
  Qed.

  Lemma xmapi_ext {A B}(f g: key -> option A -> option B) :
    (forall k (o : option A), f k o = g k o) ->
    forall m i, xmapi f m i = xmapi g m i.
  Proof.
    induction m; intros; simpl; auto. now f_equal.
  Qed.

  Theorem xmerge_commut{A B C}
    (f: key -> option A -> option B -> option C)
    (g: key -> option B -> option A -> option C) :
    (forall k o1 o2, f k o1 o2 = g k o2 o1) ->
    forall m1 m2 i, xmerge f m1 m2 i = xmerge g m2 m1 i.
  Proof.
    intros E.
    induction m1; destruct m2; intros i; simpl; trivial; f_equal;
    try apply IHm1_1; try apply IHm1_2; try apply xmapi_ext;
    intros; apply E.
  Qed.

  Theorem merge_commut{A B C}
    (f: key -> option A -> option B -> option C)
    (g: key -> option B -> option A -> option C) :
    (forall k o1 o2, f k o1 o2 = g k o2 o1) ->
    forall m1 m2, merge f m1 m2 = merge g m2 m1.
  Proof.
    intros E m1 m2.
    unfold merge. apply xmerge_commut.
    intros k [x1|] [x2|]; trivial.
  Qed.

End PositiveMapAdditionalFacts.

(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Rbase.
Require Import Rfunctions.
Local Open Scope R_scope.

Inductive Rlist : Type :=
| nil : Rlist
| cons : R -> Rlist -> Rlist.

Fixpoint In (x:R) (l:Rlist) : Prop :=
  match l with
    | nil => False
    | cons a l' => x = a \/ In x l'
  end.

Fixpoint Rlength (l:Rlist) : nat :=
  match l with
    | nil => 0%nat
    | cons a l' => S (Rlength l')
  end.

Fixpoint MaxRlist (l:Rlist) : R :=
  match l with
    | nil => 0
    | cons a l1 =>
      match l1 with
        | nil => a
        | cons a' l2 => Rmax a (MaxRlist l1)
      end
  end.

Fixpoint MinRlist (l:Rlist) : R :=
  match l with
    | nil => 1
    | cons a l1 =>
      match l1 with
        | nil => a
        | cons a' l2 => Rmin a (MinRlist l1)
      end
  end.

Lemma MaxRlist_P1 : forall (l:Rlist) (x:R), In x l -> x <= MaxRlist l.
Proof.
  intros; induction  l as [| r l Hrecl].
  simpl in H; elim H.
  induction  l as [| r0 l Hrecl0].
  simpl in H; elim H; intro.
  simpl; right; assumption.
  elim H0.
  replace (MaxRlist (cons r (cons r0 l))) with (Rmax r (MaxRlist (cons r0 l))).
  simpl in H; decompose [or] H.
  rewrite H0; apply RmaxLess1.
  unfold Rmax; case (Rle_dec r (MaxRlist (cons r0 l))); intro.
  apply Hrecl; simpl; tauto.
  apply Rle_trans with (MaxRlist (cons r0 l));
    [ apply Hrecl; simpl; tauto | left; auto with real ].
  unfold Rmax; case (Rle_dec r (MaxRlist (cons r0 l))); intro.
  apply Hrecl; simpl; tauto.
  apply Rle_trans with (MaxRlist (cons r0 l));
    [ apply Hrecl; simpl; tauto | left; auto with real ].
  reflexivity.
Qed.

Fixpoint AbsList (l:Rlist) (x:R) : Rlist :=
  match l with
    | nil => nil
    | cons a l' => cons (Rabs (a - x) / 2) (AbsList l' x)
  end.

Lemma MinRlist_P1 : forall (l:Rlist) (x:R), In x l -> MinRlist l <= x.
Proof.
  intros; induction  l as [| r l Hrecl].
  simpl in H; elim H.
  induction  l as [| r0 l Hrecl0].
  simpl in H; elim H; intro.
  simpl; right; symmetry ; assumption.
  elim H0.
  replace (MinRlist (cons r (cons r0 l))) with (Rmin r (MinRlist (cons r0 l))).
  simpl in H; decompose [or] H.
  rewrite H0; apply Rmin_l.
  unfold Rmin; case (Rle_dec r (MinRlist (cons r0 l))); intro.
  apply Rle_trans with (MinRlist (cons r0 l)).
  assumption.
  apply Hrecl; simpl; tauto.
  apply Hrecl; simpl; tauto.
  apply Rle_trans with (MinRlist (cons r0 l)).
  apply Rmin_r.
  apply Hrecl; simpl; tauto.
  reflexivity.
Qed.

Lemma AbsList_P1 :
  forall (l:Rlist) (x y:R), In y l -> In (Rabs (y - x) / 2) (AbsList l x).
Proof.
  intros; induction  l as [| r l Hrecl].
  elim H.
  simpl; simpl in H; elim H; intro.
  left; rewrite H0; reflexivity.
  right; apply Hrecl; assumption.
Qed.

Lemma MinRlist_P2 :
  forall l:Rlist, (forall y:R, In y l -> 0 < y) -> 0 < MinRlist l.
Proof.
  intros; induction  l as [| r l Hrecl].
  apply Rlt_0_1.
  induction  l as [| r0 l Hrecl0].
  simpl; apply H; simpl; tauto.
  replace (MinRlist (cons r (cons r0 l))) with (Rmin r (MinRlist (cons r0 l))).
  unfold Rmin; case (Rle_dec r (MinRlist (cons r0 l))); intro.
  apply H; simpl; tauto.
  apply Hrecl; intros; apply H; simpl; simpl in H0; tauto.
  reflexivity.
Qed.

Lemma AbsList_P2 :
  forall (l:Rlist) (x y:R),
    In y (AbsList l x) ->  exists z : R, In z l /\ y = Rabs (z - x) / 2.
Proof.
  intros; induction  l as [| r l Hrecl].
  elim H.
  elim H; intro.
  exists r; split.
  simpl; tauto.
  assumption.
  assert (H1 := Hrecl H0); elim H1; intros; elim H2; clear H2; intros;
    exists x0; simpl; simpl in H2; tauto.
Qed.

Lemma MaxRlist_P2 :
  forall l:Rlist, (exists y : R, In y l) -> In (MaxRlist l) l.
Proof.
  intros; induction  l as [| r l Hrecl].
  simpl in H; elim H; trivial.
  induction  l as [| r0 l Hrecl0].
  simpl; left; reflexivity.
  change (In (Rmax r (MaxRlist (cons r0 l))) (cons r (cons r0 l)));
    unfold Rmax; case (Rle_dec r (MaxRlist (cons r0 l)));
      intro.
  right; apply Hrecl; exists r0; left; reflexivity.
  left; reflexivity.
Qed.

Fixpoint pos_Rl (l:Rlist) (i:nat) : R :=
  match l with
    | nil => 0
    | cons a l' => match i with
                     | O => a
                     | S i' => pos_Rl l' i'
                   end
  end.

Lemma pos_Rl_P1 :
  forall (l:Rlist) (a:R),
    (0 < Rlength l)%nat ->
    pos_Rl (cons a l) (Rlength l) = pos_Rl l (pred (Rlength l)).
Proof.
  intros; induction  l as [| r l Hrecl];
    [ elim (lt_n_O _ H)
      | simpl; case (Rlength l); [ reflexivity | intro; reflexivity ] ].
Qed.

Lemma pos_Rl_P2 :
  forall (l:Rlist) (x:R),
    In x l <-> (exists i : nat, (i < Rlength l)%nat /\ x = pos_Rl l i).
Proof.
  intros; induction  l as [| r l Hrecl].
  split; intro;
    [ elim H | elim H; intros; elim H0; intros; elim (lt_n_O _ H1) ].
  split; intro.
  elim H; intro.
  exists 0%nat; split;
    [ simpl; apply lt_O_Sn | simpl; apply H0 ].
  elim Hrecl; intros; assert (H3 := H1 H0); elim H3; intros; elim H4; intros;
    exists (S x0); split;
      [ simpl; apply lt_n_S; assumption | simpl; assumption ].
  elim H; intros; elim H0; intros; destruct (zerop x0) as [->|].
  simpl in H2; left; assumption.
  right; elim Hrecl; intros H4 H5; apply H5; assert (H6 : S (pred x0) = x0).
  symmetry ; apply S_pred with 0%nat; assumption.
  exists (pred x0); split;
    [ simpl in H1; apply lt_S_n; rewrite H6; assumption
      | rewrite <- H6 in H2; simpl in H2; assumption ].
Qed.

Lemma Rlist_P1 :
  forall (l:Rlist) (P:R -> R -> Prop),
    (forall x:R, In x l ->  exists y : R, P x y) ->
    exists l' : Rlist,
      Rlength l = Rlength l' /\
      (forall i:nat, (i < Rlength l)%nat -> P (pos_Rl l i) (pos_Rl l' i)).
Proof.
  intros; induction  l as [| r l Hrecl].
  exists nil; intros; split;
    [ reflexivity | intros; simpl in H0; elim (lt_n_O _ H0) ].
  assert (H0 : In r (cons r l)).
  simpl; left; reflexivity.
  assert (H1 := H _ H0);
    assert (H2 : forall x:R, In x l ->  exists y : R, P x y).
  intros; apply H; simpl; right; assumption.
  assert (H3 := Hrecl H2); elim H1; intros; elim H3; intros; exists (cons x x0);
    intros; elim H5; clear H5; intros; split.
  simpl; rewrite H5; reflexivity.
  intros; destruct (zerop i) as [->|].
  simpl; assumption.
  assert (H9 : i = S (pred i)).
  apply S_pred with 0%nat; assumption.
  rewrite H9; simpl; apply H6; simpl in H7; apply lt_S_n; rewrite <- H9;
    assumption.
Qed.

Definition ordered_Rlist (l:Rlist) : Prop :=
  forall i:nat, (i < pred (Rlength l))%nat -> pos_Rl l i <= pos_Rl l (S i).

Fixpoint insert (l:Rlist) (x:R) : Rlist :=
  match l with
    | nil => cons x nil
    | cons a l' =>
      match Rle_dec a x with
        | left _ => cons a (insert l' x)
        | right _ => cons x l
      end
  end.

Fixpoint cons_Rlist (l k:Rlist) : Rlist :=
  match l with
    | nil => k
    | cons a l' => cons a (cons_Rlist l' k)
  end.

Fixpoint cons_ORlist (k l:Rlist) : Rlist :=
  match k with
    | nil => l
    | cons a k' => cons_ORlist k' (insert l a)
  end.

Fixpoint app_Rlist (l:Rlist) (f:R -> R) : Rlist :=
  match l with
    | nil => nil
    | cons a l' => cons (f a) (app_Rlist l' f)
  end.

Fixpoint mid_Rlist (l:Rlist) (x:R) : Rlist :=
  match l with
    | nil => nil
    | cons a l' => cons ((x + a) / 2) (mid_Rlist l' a)
  end.

Definition Rtail (l:Rlist) : Rlist :=
  match l with
    | nil => nil
    | cons a l' => l'
  end.

Definition FF (l:Rlist) (f:R -> R) : Rlist :=
  match l with
    | nil => nil
    | cons a l' => app_Rlist (mid_Rlist l' a) f
  end.

Lemma RList_P0 :
  forall (l:Rlist) (a:R),
    pos_Rl (insert l a) 0 = a \/ pos_Rl (insert l a) 0 = pos_Rl l 0.
Proof.
  intros; induction  l as [| r l Hrecl];
    [ left; reflexivity
      | simpl; case (Rle_dec r a); intro;
        [ right; reflexivity | left; reflexivity ] ].
Qed.

Lemma RList_P1 :
  forall (l:Rlist) (a:R), ordered_Rlist l -> ordered_Rlist (insert l a).
Proof.
  intros; induction  l as [| r l Hrecl].
  simpl; unfold ordered_Rlist; intros; simpl in H0;
    elim (lt_n_O _ H0).
  simpl; case (Rle_dec r a); intro.
  assert (H1 : ordered_Rlist l).
  unfold ordered_Rlist; unfold ordered_Rlist in H; intros;
    assert (H1 : (S i < pred (Rlength (cons r l)))%nat);
      [ simpl; replace (Rlength l) with (S (pred (Rlength l)));
        [ apply lt_n_S; assumption
          | symmetry ; apply S_pred with 0%nat; apply neq_O_lt; red;
            intro; rewrite <- H1 in H0; simpl in H0; elim (lt_n_O _ H0) ]
        | apply (H _ H1) ].
  assert (H2 := Hrecl H1); unfold ordered_Rlist; intros;
    induction  i as [| i Hreci].
  simpl; assert (H3 := RList_P0 l a); elim H3; intro.
  rewrite H4; assumption.
  induction  l as [| r1 l Hrecl0];
    [ simpl; assumption
      | rewrite H4; apply (H 0%nat); simpl; apply lt_O_Sn ].
  simpl; apply H2; simpl in H0; apply lt_S_n;
    replace (S (pred (Rlength (insert l a)))) with (Rlength (insert l a));
    [ assumption
      | apply S_pred with 0%nat; apply neq_O_lt; red; intro;
        rewrite <- H3 in H0; elim (lt_n_O _ H0) ].
  unfold ordered_Rlist; intros; induction  i as [| i Hreci];
    [ simpl; auto with real
      | change (pos_Rl (cons r l) i <= pos_Rl (cons r l) (S i)); apply H;
        simpl in H0; simpl; apply (lt_S_n _ _ H0) ].
Qed.

Lemma RList_P2 :
  forall l1 l2:Rlist, ordered_Rlist l2 -> ordered_Rlist (cons_ORlist l1 l2).
Proof.
  simple induction l1;
    [ intros; simpl; apply H
      | intros; simpl; apply H; apply RList_P1; assumption ].
Qed.

Lemma RList_P3 :
  forall (l:Rlist) (x:R),
    In x l <-> (exists i : nat, x = pos_Rl l i /\ (i < Rlength l)%nat).
Proof.
  intros; split; intro;
    [ induction  l as [| r l Hrecl] | induction  l as [| r l Hrecl] ].
  elim H.
  elim H; intro;
    [ exists 0%nat; split; [ apply H0 | simpl; apply lt_O_Sn ]
      | elim (Hrecl H0); intros; elim H1; clear H1; intros; exists (S x0); split;
        [ apply H1 | simpl; apply lt_n_S; assumption ] ].
  elim H; intros; elim H0; intros; elim (lt_n_O _ H2).
  simpl; elim H; intros; elim H0; clear H0; intros;
    induction  x0 as [| x0 Hrecx0];
      [ left; apply H0
        | right; apply Hrecl; exists x0; split;
          [ apply H0 | simpl in H1; apply lt_S_n; assumption ] ].
Qed.

Lemma RList_P4 :
  forall (l1:Rlist) (a:R), ordered_Rlist (cons a l1) -> ordered_Rlist l1.
Proof.
  intros; unfold ordered_Rlist; intros; apply (H (S i)); simpl;
    replace (Rlength l1) with (S (pred (Rlength l1)));
    [ apply lt_n_S; assumption
      | symmetry ; apply S_pred with 0%nat; apply neq_O_lt; red;
        intro; rewrite <- H1 in H0; elim (lt_n_O _ H0) ].
Qed.

Lemma RList_P5 :
  forall (l:Rlist) (x:R), ordered_Rlist l -> In x l -> pos_Rl l 0 <= x.
Proof.
  intros; induction  l as [| r l Hrecl];
    [ elim H0
      | simpl; elim H0; intro;
        [ rewrite H1; right; reflexivity
          | apply Rle_trans with (pos_Rl l 0);
            [ apply (H 0%nat); simpl; induction  l as [| r0 l Hrecl0];
              [ elim H1 | simpl; apply lt_O_Sn ]
              | apply Hrecl; [ eapply RList_P4; apply H | assumption ] ] ] ].
Qed.

Lemma RList_P6 :
  forall l:Rlist,
    ordered_Rlist l <->
    (forall i j:nat,
      (i <= j)%nat -> (j < Rlength l)%nat -> pos_Rl l i <= pos_Rl l j).
Proof.
  simple induction l; split; intro.
  intros; right; reflexivity.
  unfold ordered_Rlist; intros; simpl in H0; elim (lt_n_O _ H0).
  intros; induction  i as [| i Hreci];
    [ induction  j as [| j Hrecj];
      [ right; reflexivity
        | simpl; apply Rle_trans with (pos_Rl r0 0);
          [ apply (H0 0%nat); simpl; simpl in H2; apply neq_O_lt;
            red; intro; rewrite <- H3 in H2;
              assert (H4 := lt_S_n _ _ H2); elim (lt_n_O _ H4)
            | elim H; intros; apply H3;
              [ apply RList_P4 with r; assumption
                | apply le_O_n
                | simpl in H2; apply lt_S_n; assumption ] ] ]
      | induction  j as [| j Hrecj];
        [ elim (le_Sn_O _ H1)
          | simpl; elim H; intros; apply H3;
            [ apply RList_P4 with r; assumption
              | apply le_S_n; assumption
              | simpl in H2; apply lt_S_n; assumption ] ] ].
  unfold ordered_Rlist; intros; apply H0;
    [ apply le_n_Sn | simpl; simpl in H1; apply lt_n_S; assumption ].
Qed.

Lemma RList_P7 :
  forall (l:Rlist) (x:R),
    ordered_Rlist l -> In x l -> x <= pos_Rl l (pred (Rlength l)).
Proof.
  intros; assert (H1 := RList_P6 l); elim H1; intros H2 _; assert (H3 := H2 H);
    clear H1 H2; assert (H1 := RList_P3 l x); elim H1;
      clear H1; intros; assert (H4 := H1 H0); elim H4; clear H4;
        intros; elim H4; clear H4; intros; rewrite H4;
          assert (H6 : Rlength l = S (pred (Rlength l))).
  apply S_pred with 0%nat; apply neq_O_lt; red; intro;
    rewrite <- H6 in H5; elim (lt_n_O _ H5).
  apply H3;
    [ rewrite H6 in H5; apply lt_n_Sm_le; assumption
      | apply lt_pred_n_n; apply neq_O_lt; red; intro; rewrite <- H7 in H5;
        elim (lt_n_O _ H5) ].
Qed.

Lemma RList_P8 :
  forall (l:Rlist) (a x:R), In x (insert l a) <-> x = a \/ In x l.
Proof.
  simple induction l.
  intros; split; intro; simpl in H; apply H.
  intros; split; intro;
    [ simpl in H0; generalize H0; case (Rle_dec r a); intros;
      [ simpl in H1; elim H1; intro;
        [ right; left; assumption
          | elim (H a x); intros; elim (H3 H2); intro;
            [ left; assumption | right; right; assumption ] ]
        | simpl in H1; decompose [or] H1;
          [ left; assumption
            | right; left; assumption
            | right; right; assumption ] ]
      | simpl; case (Rle_dec r a); intro;
        [ simpl in H0; decompose [or] H0;
          [ right; elim (H a x); intros; apply H3; left
            | left
            | right; elim (H a x); intros; apply H3; right ]
          | simpl in H0; decompose [or] H0; [ left | right; left | right; right ] ];
        assumption ].
Qed.

Lemma RList_P9 :
  forall (l1 l2:Rlist) (x:R), In x (cons_ORlist l1 l2) <-> In x l1 \/ In x l2.
Proof.
  simple induction l1.
  intros; split; intro;
    [ simpl in H; right; assumption
      | simpl; elim H; intro; [ elim H0 | assumption ] ].
  intros; split.
  simpl; intros; elim (H (insert l2 r) x); intros; assert (H3 := H1 H0);
    elim H3; intro;
      [ left; right; assumption
        | elim (RList_P8 l2 r x); intros H5 _; assert (H6 := H5 H4); elim H6; intro;
          [ left; left; assumption | right; assumption ] ].
  intro; simpl; elim (H (insert l2 r) x); intros _ H1; apply H1;
    elim H0; intro;
      [ elim H2; intro;
        [ right; elim (RList_P8 l2 r x); intros _ H4; apply H4; left; assumption
          | left; assumption ]
        | right; elim (RList_P8 l2 r x); intros _ H3; apply H3; right; assumption ].
Qed.

Lemma RList_P10 :
  forall (l:Rlist) (a:R), Rlength (insert l a) = S (Rlength l).
Proof.
  intros; induction  l as [| r l Hrecl];
    [ reflexivity
      | simpl; case (Rle_dec r a); intro;
        [ simpl; rewrite Hrecl; reflexivity | reflexivity ] ].
Qed.

Lemma RList_P11 :
  forall l1 l2:Rlist,
    Rlength (cons_ORlist l1 l2) = (Rlength l1 + Rlength l2)%nat.
Proof.
  simple induction l1;
    [ intro; reflexivity
      | intros; simpl; rewrite (H (insert l2 r)); rewrite RList_P10;
        apply INR_eq; rewrite S_INR; do 2 rewrite plus_INR;
          rewrite S_INR; ring ].
Qed.

Lemma RList_P12 :
  forall (l:Rlist) (i:nat) (f:R -> R),
    (i < Rlength l)%nat -> pos_Rl (app_Rlist l f) i = f (pos_Rl l i).
Proof.
  simple induction l;
    [ intros; elim (lt_n_O _ H)
      | intros; induction  i as [| i Hreci];
        [ reflexivity | simpl; apply H; apply lt_S_n; apply H0 ] ].
Qed.

Lemma RList_P13 :
  forall (l:Rlist) (i:nat) (a:R),
    (i < pred (Rlength l))%nat ->
    pos_Rl (mid_Rlist l a) (S i) = (pos_Rl l i + pos_Rl l (S i)) / 2.
Proof.
  simple induction l.
  intros; simpl in H; elim (lt_n_O _ H).
  simple induction r0.
  intros; simpl in H0; elim (lt_n_O _ H0).
  intros; simpl in H1; induction  i as [| i Hreci].
  reflexivity.
  change
    (pos_Rl (mid_Rlist (cons r1 r2) r) (S i) =
      (pos_Rl (cons r1 r2) i + pos_Rl (cons r1 r2) (S i)) / 2)
   ; apply H0; simpl; apply lt_S_n; assumption.
Qed.

Lemma RList_P14 : forall (l:Rlist) (a:R), Rlength (mid_Rlist l a) = Rlength l.
Proof.
  simple induction l; intros;
    [ reflexivity | simpl; rewrite (H r); reflexivity ].
Qed.

Lemma RList_P15 :
  forall l1 l2:Rlist,
    ordered_Rlist l1 ->
    ordered_Rlist l2 ->
    pos_Rl l1 0 = pos_Rl l2 0 -> pos_Rl (cons_ORlist l1 l2) 0 = pos_Rl l1 0.
Proof.
  intros; apply Rle_antisym.
  induction  l1 as [| r l1 Hrecl1];
    [ simpl; simpl in H1; right; symmetry ; assumption
      | elim (RList_P9 (cons r l1) l2 (pos_Rl (cons r l1) 0)); intros;
        assert
          (H4 :
            In (pos_Rl (cons r l1) 0) (cons r l1) \/ In (pos_Rl (cons r l1) 0) l2);
          [ left; left; reflexivity
            | assert (H5 := H3 H4); apply RList_P5;
              [ apply RList_P2; assumption | assumption ] ] ].
  induction  l1 as [| r l1 Hrecl1];
    [ simpl; simpl in H1; right; assumption
      | assert
        (H2 :
          In (pos_Rl (cons_ORlist (cons r l1) l2) 0) (cons_ORlist (cons r l1) l2));
        [ elim
          (RList_P3 (cons_ORlist (cons r l1) l2)
            (pos_Rl (cons_ORlist (cons r l1) l2) 0));
          intros; apply H3; exists 0%nat; split;
            [ reflexivity | rewrite RList_P11; simpl; apply lt_O_Sn ]
          | elim (RList_P9 (cons r l1) l2 (pos_Rl (cons_ORlist (cons r l1) l2) 0));
            intros; assert (H5 := H3 H2); elim H5; intro;
              [ apply RList_P5; assumption
                | rewrite H1; apply RList_P5; assumption ] ] ].
Qed.

Lemma RList_P16 :
  forall l1 l2:Rlist,
    ordered_Rlist l1 ->
    ordered_Rlist l2 ->
    pos_Rl l1 (pred (Rlength l1)) = pos_Rl l2 (pred (Rlength l2)) ->
    pos_Rl (cons_ORlist l1 l2) (pred (Rlength (cons_ORlist l1 l2))) =
    pos_Rl l1 (pred (Rlength l1)).
Proof.
  intros; apply Rle_antisym.
  induction  l1 as [| r l1 Hrecl1].
  simpl; simpl in H1; right; symmetry ; assumption.
  assert
    (H2 :
      In
      (pos_Rl (cons_ORlist (cons r l1) l2)
        (pred (Rlength (cons_ORlist (cons r l1) l2))))
      (cons_ORlist (cons r l1) l2));
    [ elim
      (RList_P3 (cons_ORlist (cons r l1) l2)
        (pos_Rl (cons_ORlist (cons r l1) l2)
          (pred (Rlength (cons_ORlist (cons r l1) l2)))));
      intros; apply H3; exists (pred (Rlength (cons_ORlist (cons r l1) l2)));
        split; [ reflexivity | rewrite RList_P11; simpl; apply lt_n_Sn ]
      | elim
        (RList_P9 (cons r l1) l2
          (pos_Rl (cons_ORlist (cons r l1) l2)
            (pred (Rlength (cons_ORlist (cons r l1) l2)))));
        intros; assert (H5 := H3 H2); elim H5; intro;
          [ apply RList_P7; assumption | rewrite H1; apply RList_P7; assumption ] ].
  induction  l1 as [| r l1 Hrecl1].
  simpl; simpl in H1; right; assumption.
  elim
    (RList_P9 (cons r l1) l2 (pos_Rl (cons r l1) (pred (Rlength (cons r l1)))));
    intros;
      assert
        (H4 :
          In (pos_Rl (cons r l1) (pred (Rlength (cons r l1)))) (cons r l1) \/
          In (pos_Rl (cons r l1) (pred (Rlength (cons r l1)))) l2);
        [ left; change (In (pos_Rl (cons r l1) (Rlength l1)) (cons r l1));
          elim (RList_P3 (cons r l1) (pos_Rl (cons r l1) (Rlength l1)));
            intros; apply H5; exists (Rlength l1); split;
              [ reflexivity | simpl; apply lt_n_Sn ]
          | assert (H5 := H3 H4); apply RList_P7;
            [ apply RList_P2; assumption
              | elim
                (RList_P9 (cons r l1) l2
                  (pos_Rl (cons r l1) (pred (Rlength (cons r l1)))));
                intros; apply H7; left;
                  elim
                    (RList_P3 (cons r l1)
                      (pos_Rl (cons r l1) (pred (Rlength (cons r l1)))));
                    intros; apply H9; exists (pred (Rlength (cons r l1)));
                      split; [ reflexivity | simpl; apply lt_n_Sn ] ] ].
Qed.

Lemma RList_P17 :
  forall (l1:Rlist) (x:R) (i:nat),
    ordered_Rlist l1 ->
    In x l1 ->
    pos_Rl l1 i < x -> (i < pred (Rlength l1))%nat -> pos_Rl l1 (S i) <= x.
Proof.
  simple induction l1.
  intros; elim H0.
  intros; induction  i as [| i Hreci].
  simpl; elim H1; intro;
    [ simpl in H2; rewrite H4 in H2; elim (Rlt_irrefl _ H2)
      | apply RList_P5; [ apply RList_P4 with r; assumption | assumption ] ].
  simpl; simpl in H2; elim H1; intro.
  rewrite H4 in H2; assert (H5 : r <= pos_Rl r0 i);
    [ apply Rle_trans with (pos_Rl r0 0);
      [ apply (H0 0%nat); simpl; simpl in H3; apply neq_O_lt;
        red; intro; rewrite <- H5 in H3; elim (lt_n_O _ H3)
        | elim (RList_P6 r0); intros; apply H5;
          [ apply RList_P4 with r; assumption
            | apply le_O_n
            | simpl in H3; apply lt_S_n; apply lt_trans with (Rlength r0);
              [ apply H3 | apply lt_n_Sn ] ] ]
      | elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H5 H2)) ].
  apply H; try assumption;
    [ apply RList_P4 with r; assumption
      | simpl in H3; apply lt_S_n;
        replace (S (pred (Rlength r0))) with (Rlength r0);
        [ apply H3
          | apply S_pred with 0%nat; apply neq_O_lt; red; intro;
            rewrite <- H5 in H3; elim (lt_n_O _ H3) ] ].
Qed.

Lemma RList_P18 :
  forall (l:Rlist) (f:R -> R), Rlength (app_Rlist l f) = Rlength l.
Proof.
  simple induction l; intros;
    [ reflexivity | simpl; rewrite H; reflexivity ].
Qed.

Lemma RList_P19 :
  forall l:Rlist,
    l <> nil ->  exists r : R, (exists r0 : Rlist, l = cons r r0).
Proof.
  intros; induction  l as [| r l Hrecl];
    [ elim H; reflexivity | exists r; exists l; reflexivity ].
Qed.

Lemma RList_P20 :
  forall l:Rlist,
    (2 <= Rlength l)%nat ->
    exists r : R,
      (exists r1 : R, (exists l' : Rlist, l = cons r (cons r1 l'))).
Proof.
  intros; induction  l as [| r l Hrecl];
    [ simpl in H; elim (le_Sn_O _ H)
      | induction  l as [| r0 l Hrecl0];
        [ simpl in H; elim (le_Sn_O _ (le_S_n _ _ H))
          | exists r; exists r0; exists l; reflexivity ] ].
Qed.

Lemma RList_P21 : forall l l':Rlist, l = l' -> Rtail l = Rtail l'.
Proof.
  intros; rewrite H; reflexivity.
Qed.

Lemma RList_P22 :
  forall l1 l2:Rlist, l1 <> nil -> pos_Rl (cons_Rlist l1 l2) 0 = pos_Rl l1 0.
Proof.
  simple induction l1; [ intros; elim H; reflexivity | intros; reflexivity ].
Qed.

Lemma RList_P23 :
  forall l1 l2:Rlist,
    Rlength (cons_Rlist l1 l2) = (Rlength l1 + Rlength l2)%nat.
Proof.
  simple induction l1;
    [ intro; reflexivity | intros; simpl; rewrite H; reflexivity ].
Qed.

Lemma RList_P24 :
  forall l1 l2:Rlist,
    l2 <> nil ->
    pos_Rl (cons_Rlist l1 l2) (pred (Rlength (cons_Rlist l1 l2))) =
    pos_Rl l2 (pred (Rlength l2)).
Proof.
  simple induction l1.
  intros; reflexivity.
  intros; rewrite <- (H l2 H0); induction  l2 as [| r1 l2 Hrecl2].
  elim H0; reflexivity.
  do 2 rewrite RList_P23;
    replace (Rlength (cons r r0) + Rlength (cons r1 l2))%nat with
    (S (S (Rlength r0 + Rlength l2)));
    [ replace (Rlength r0 + Rlength (cons r1 l2))%nat with
      (S (Rlength r0 + Rlength l2));
      [ reflexivity
        | simpl; apply INR_eq; rewrite S_INR; do 2 rewrite plus_INR;
          rewrite S_INR; ring ]
      | simpl; apply INR_eq; do 3 rewrite S_INR; do 2 rewrite plus_INR;
        rewrite S_INR; ring ].
Qed.

Lemma RList_P25 :
  forall l1 l2:Rlist,
    ordered_Rlist l1 ->
    ordered_Rlist l2 ->
    pos_Rl l1 (pred (Rlength l1)) <= pos_Rl l2 0 ->
    ordered_Rlist (cons_Rlist l1 l2).
Proof.
  simple induction l1.
  intros; simpl; assumption.
  simple induction r0.
  intros; simpl; simpl in H2; unfold ordered_Rlist; intros;
    simpl in H3.
  induction  i as [| i Hreci].
  simpl; assumption.
  change (pos_Rl l2 i <= pos_Rl l2 (S i)); apply (H1 i); apply lt_S_n;
    replace (S (pred (Rlength l2))) with (Rlength l2);
    [ assumption
      | apply S_pred with 0%nat; apply neq_O_lt; red; intro;
        rewrite <- H4 in H3; elim (lt_n_O _ H3) ].
  intros; clear H; assert (H : ordered_Rlist (cons_Rlist (cons r1 r2) l2)).
  apply H0; try assumption.
  apply RList_P4 with r; assumption.
  unfold ordered_Rlist; intros; simpl in H4;
    induction  i as [| i Hreci].
  simpl; apply (H1 0%nat); simpl; apply lt_O_Sn.
  change
    (pos_Rl (cons_Rlist (cons r1 r2) l2) i <=
      pos_Rl (cons_Rlist (cons r1 r2) l2) (S i));
    apply (H i); simpl; apply lt_S_n; assumption.
Qed.

Lemma RList_P26 :
  forall (l1 l2:Rlist) (i:nat),
    (i < Rlength l1)%nat -> pos_Rl (cons_Rlist l1 l2) i = pos_Rl l1 i.
Proof.
  simple induction l1.
  intros; elim (lt_n_O _ H).
  intros; induction  i as [| i Hreci].
  apply RList_P22; discriminate.
  apply (H l2 i); simpl in H0; apply lt_S_n; assumption.
Qed.

Lemma RList_P27 :
  forall l1 l2 l3:Rlist,
    cons_Rlist l1 (cons_Rlist l2 l3) = cons_Rlist (cons_Rlist l1 l2) l3.
Proof.
  simple induction l1; intros;
    [ reflexivity | simpl; rewrite (H l2 l3); reflexivity ].
Qed.

Lemma RList_P28 : forall l:Rlist, cons_Rlist l nil = l.
Proof.
  simple induction l;
    [ reflexivity | intros; simpl; rewrite H; reflexivity ].
Qed.

Lemma RList_P29 :
  forall (l2 l1:Rlist) (i:nat),
    (Rlength l1 <= i)%nat ->
    (i < Rlength (cons_Rlist l1 l2))%nat ->
    pos_Rl (cons_Rlist l1 l2) i = pos_Rl l2 (i - Rlength l1).
Proof.
  simple induction l2.
  intros; rewrite RList_P28 in H0; elim (lt_irrefl _ (le_lt_trans _ _ _ H H0)).
  intros;
    replace (cons_Rlist l1 (cons r r0)) with
    (cons_Rlist (cons_Rlist l1 (cons r nil)) r0).
  inversion H0.
  rewrite <- minus_n_n; simpl; rewrite RList_P26.
  clear l2 r0 H i H0 H1 H2; induction  l1 as [| r0 l1 Hrecl1].
  reflexivity.
  simpl; assumption.
  rewrite RList_P23; rewrite plus_comm; simpl; apply lt_n_Sn.
  replace (S m - Rlength l1)%nat with (S (S m - S (Rlength l1))).
  rewrite H3; simpl;
    replace (S (Rlength l1)) with (Rlength (cons_Rlist l1 (cons r nil))).
  apply (H (cons_Rlist l1 (cons r nil)) i).
  rewrite RList_P23; rewrite plus_comm; simpl; rewrite <- H3;
    apply le_n_S; assumption.
  repeat rewrite RList_P23; simpl; rewrite RList_P23 in H1;
    rewrite plus_comm in H1; simpl in H1; rewrite (plus_comm (Rlength l1));
      simpl; rewrite plus_comm; apply H1.
  rewrite RList_P23; rewrite plus_comm; reflexivity.
  change (S (m - Rlength l1) = (S m - Rlength l1)%nat);
    apply minus_Sn_m; assumption.
  replace (cons r r0) with (cons_Rlist (cons r nil) r0);
  [ symmetry ; apply RList_P27 | reflexivity ].
Qed.

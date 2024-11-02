(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import List.
Require Import Compare_dec.
Require Import Rbase.
Require Import Rfunctions.
Local Open Scope R_scope.

Fixpoint MaxRlist (l:list R) : R :=
  match l with
    | nil => 0
    | a :: l1 =>
      match l1 with
        | nil => a
        | a' :: l2 => Rmax a (MaxRlist l1)
      end
  end.

Fixpoint MinRlist (l:list R) : R :=
  match l with
    | nil => 1
    | a :: l1 =>
      match l1 with
        | nil => a
        | a' :: l2 => Rmin a (MinRlist l1)
      end
  end.

Lemma MaxRlist_P1 : forall (l:list R) (x:R), In x l -> x <= MaxRlist l.
Proof.
  intros; induction  l as [| r l Hrecl].
  - simpl in H; elim H.
  - induction  l as [| r0 l Hrecl0].
    + simpl in H; elim H; intro.
      * simpl; right; symmetry; assumption.
      * elim H0.
    + replace (MaxRlist (r :: r0 :: l)) with (Rmax r (MaxRlist (r0 :: l))).
      * simpl in H; decompose [or] H.
        -- rewrite H0; apply RmaxLess1.
        -- unfold Rmax; case (Rle_dec r (MaxRlist (r0 :: l))); intro.
           ++ apply Hrecl; simpl; tauto.
           ++ apply Rle_trans with (MaxRlist (r0 :: l));
                [ apply Hrecl; simpl; tauto | left; auto with real ].
        -- unfold Rmax; case (Rle_dec r (MaxRlist (r0 :: l))); intro.
           ++ apply Hrecl; simpl; tauto.
           ++ apply Rle_trans with (MaxRlist (r0 :: l));
                [ apply Hrecl; simpl; tauto | left; auto with real ].
      * reflexivity.
Qed.

Fixpoint AbsList (l:list R) (x:R) : list R :=
  match l with
    | nil => nil
    | a :: l' => (Rabs (a - x) / 2) :: (AbsList l' x)
  end.

Lemma MinRlist_P1 : forall (l:list R) (x:R), In x l -> MinRlist l <= x.
Proof.
  intros; induction  l as [| r l Hrecl].
  - simpl in H; elim H.
  - induction  l as [| r0 l Hrecl0].
    + simpl in H; elim H; intro.
      * simpl; right; assumption.
      * elim H0.
    + replace (MinRlist (r :: r0 :: l)) with (Rmin r (MinRlist (r0 :: l))).
      * simpl in H; decompose [or] H.
        -- rewrite H0; apply Rmin_l.
        -- unfold Rmin; case (Rle_dec r (MinRlist (r0 :: l))); intro.
           ++ apply Rle_trans with (MinRlist (r0 :: l)).
              ** assumption.
              ** apply Hrecl; simpl; tauto.
           ++ apply Hrecl; simpl; tauto.
        -- apply Rle_trans with (MinRlist (r0 :: l)).
           ++ apply Rmin_r.
           ++ apply Hrecl; simpl; tauto.
      * reflexivity.
Qed.

Lemma AbsList_P1 :
  forall (l:list R) (x y:R), In y l -> In (Rabs (y - x) / 2) (AbsList l x).
Proof.
  intros; induction  l as [| r l Hrecl].
  - elim H.
  - simpl; simpl in H; elim H; intro.
    + left; rewrite H0; reflexivity.
    + right; apply Hrecl; assumption.
Qed.

Lemma MinRlist_P2 :
  forall l:list R, (forall y:R, In y l -> 0 < y) -> 0 < MinRlist l.
Proof.
  intros; induction  l as [| r l Hrecl].
  - apply Rlt_0_1.
  - induction  l as [| r0 l Hrecl0].
    + simpl; apply H; simpl; tauto.
    + replace (MinRlist (r :: r0 :: l)) with (Rmin r (MinRlist (r0 :: l))).
      * unfold Rmin; case (Rle_dec r (MinRlist (r0 :: l))); intro.
        -- apply H; simpl; tauto.
        -- apply Hrecl; intros; apply H; simpl; simpl in H0; tauto.
      * reflexivity.
Qed.

Lemma AbsList_P2 :
  forall (l:list R) (x y:R),
    In y (AbsList l x) ->  exists z : R, In z l /\ y = Rabs (z - x) / 2.
Proof.
  intros; induction  l as [| r l Hrecl].
  - elim H.
  - elim H; intro.
    + exists r; split.
      * simpl; tauto.
      * symmetry.
        assumption.
    + assert (H1 := Hrecl H0); elim H1; intros; elim H2; clear H2; intros;
        exists x0; simpl; simpl in H2; tauto.
Qed.

Lemma MaxRlist_P2 :
  forall l:list R, (exists y : R, In y l) -> In (MaxRlist l) l.
Proof.
  intros; induction  l as [| r l Hrecl].
  - simpl in H; elim H; trivial.
  - induction  l as [| r0 l Hrecl0].
    + simpl; left; reflexivity.
    + change (In (Rmax r (MaxRlist (r0 :: l))) (r :: r0 :: l));
        unfold Rmax; case (Rle_dec r (MaxRlist (r0 :: l)));
        intro.
      * right; apply Hrecl; exists r0; left; reflexivity.
      * left; reflexivity.
Qed.

Fixpoint pos_Rl (l:list R) (i:nat) : R :=
  match l with
    | nil => 0
    | a :: l' => match i with
                     | O => a
                     | S i' => pos_Rl l' i'
                   end
  end.

Lemma pos_Rl_P1 :
  forall (l:list R) (a:R),
    (0 < length l)%nat ->
    pos_Rl (a :: l) (length l) = pos_Rl l (pred (length l)).
Proof.
  intros; induction  l as [| r l Hrecl];
    [ elim (Nat.nlt_0_r _ H)
      | simpl; case (length l); [ reflexivity | intro; reflexivity ] ].
Qed.

Lemma pos_Rl_P2 :
  forall (l:list R) (x:R),
    In x l <-> (exists i : nat, (i < length l)%nat /\ x = pos_Rl l i).
Proof.
  intros; induction  l as [| r l Hrecl].
  - split; intro;
      [ elim H | elim H; intros; elim H0; intros; elim (Nat.nlt_0_r _ H1) ].
  - split; intro.
    + elim H; intro.
      * exists 0%nat; split;
          [ simpl; apply Nat.lt_0_succ | simpl; symmetry; apply H0 ].
      * elim Hrecl; intros; assert (H3 := H1 H0); elim H3; intros; elim H4; intros;
          exists (S x0); split;
          [ simpl; apply -> Nat.succ_lt_mono; assumption | simpl; assumption ].
    + elim H; intros; elim H0; intros; destruct (zerop x0) as [->|].
      * simpl in H2; left; symmetry; assumption.
      * right; elim Hrecl; intros H4 H5; apply H5; assert (H6 : S (pred x0) = x0).
        -- apply Nat.lt_succ_pred with 0%nat; assumption.
        -- exists (pred x0); split;
             [ simpl in H1; apply Nat.succ_lt_mono; rewrite H6; assumption
             | rewrite <- H6 in H2; simpl in H2; assumption ].
Qed.

Lemma Rlist_P1 :
  forall (l:list R) (P:R -> R -> Prop),
    (forall x:R, In x l ->  exists y : R, P x y) ->
    exists l' : list R,
      length l = length l' /\
      (forall i:nat, (i < length l)%nat -> P (pos_Rl l i) (pos_Rl l' i)).
Proof.
  intros; induction  l as [| r l Hrecl].
  - exists nil; intros; split;
      [ reflexivity | intros; simpl in H0; elim (Nat.nlt_0_r _ H0) ].
  - assert (H0 : In r (r :: l)).
    + simpl; left; reflexivity.
    + assert (H1 := H _ H0);
        assert (H2 : forall x:R, In x l ->  exists y : R, P x y).
      * intros; apply H; simpl; right; assumption.
      * assert (H3 := Hrecl H2); elim H1; intros; elim H3; intros; exists (x :: x0);
          intros; elim H5; clear H5; intros; split.
        -- simpl; rewrite H5; reflexivity.
        -- intros; destruct (zerop i) as [->|].
           ++ simpl; assumption.
           ++ assert (H9 : i = S (pred i)).
              ** symmetry; apply Nat.lt_succ_pred with 0%nat; assumption.
              ** rewrite H9; simpl; apply H6; simpl in H7; apply Nat.succ_lt_mono; rewrite <- H9;
                   assumption.
Qed.

Definition ordered_Rlist (l:list R) : Prop :=
  forall i:nat, (i < pred (length l))%nat -> pos_Rl l i <= pos_Rl l (S i).

Fixpoint insert (l:list R) (x:R) : list R :=
  match l with
    | nil => x :: nil
    | a :: l' =>
      match Rle_dec a x with
        | left _ => a :: (insert l' x)
        | right _ => x :: l
      end
  end.

Fixpoint cons_ORlist (k l:list R) : list R :=
  match k with
    | nil => l
    | a :: k' => cons_ORlist k' (insert l a)
  end.

Fixpoint mid_Rlist (l:list R) (x:R) : list R :=
  match l with
    | nil => nil
    | a :: l' => ((x + a) / 2) :: (mid_Rlist l' a)
  end.

Definition Rtail (l:list R) : list R :=
  match l with
    | nil => nil
    |  a :: l' => l'
  end.

Definition FF (l:list R) (f:R -> R) : list R :=
  match l with
    | nil => nil
    | a :: l' => map f (mid_Rlist l' a)
  end.

Lemma RList_P0 :
  forall (l:list R) (a:R),
    pos_Rl (insert l a) 0 = a \/ pos_Rl (insert l a) 0 = pos_Rl l 0.
Proof.
  intros; induction  l as [| r l Hrecl];
    [ left; reflexivity
      | simpl; case (Rle_dec r a); intro;
        [ right; reflexivity | left; reflexivity ] ].
Qed.

Lemma RList_P1 :
  forall (l:list R) (a:R), ordered_Rlist l -> ordered_Rlist (insert l a).
Proof.
  intros; induction  l as [| r l Hrecl].
  - simpl; unfold ordered_Rlist; intros; simpl in H0;
      elim (Nat.nlt_0_r _ H0).
  - simpl; case (Rle_dec r a); intro.
    + assert (H1 : ordered_Rlist l).
      * unfold ordered_Rlist; unfold ordered_Rlist in H; intros;
          assert (H1 : (S i < pred (length (r :: l)))%nat);
          [ simpl; replace (length l) with (S (pred (length l)));
            [ apply -> Nat.succ_lt_mono; assumption
            | apply Nat.lt_succ_pred with 0%nat; apply Nat.neq_0_lt_0; red;
              intro; rewrite H1 in H0; simpl in H0; elim (Nat.nlt_0_r _ H0) ]
          | apply (H _ H1) ].
      * assert (H2 := Hrecl H1); unfold ordered_Rlist; intros;
          induction  i as [| i Hreci].
        -- simpl; assert (H3 := RList_P0 l a); elim H3; intro.
           ++ rewrite H4; assumption.
           ++ induction  l as [| r1 l Hrecl0];
                [ simpl; assumption
                | rewrite H4; apply (H 0%nat); simpl; apply Nat.lt_0_succ ].
        -- simpl; apply H2; simpl in H0; apply Nat.succ_lt_mono;
             replace (S (pred (length (insert l a)))) with (length (insert l a));
             [ assumption
             | symmetry; apply Nat.lt_succ_pred with 0%nat; apply Nat.neq_0_lt_0; red; intro;
               rewrite H3 in H0; elim (Nat.nlt_0_r _ H0) ].
    + unfold ordered_Rlist; intros; induction  i as [| i Hreci];
        [ simpl; auto with real
        | change (pos_Rl (r :: l) i <= pos_Rl (r :: l) (S i)); apply H;
          simpl in H0; simpl; apply (proj2 (Nat.succ_lt_mono _ _) H0) ].
Qed.

Lemma RList_P2 :
  forall l1 l2:list R, ordered_Rlist l2 -> ordered_Rlist (cons_ORlist l1 l2).
Proof.
  simple induction l1;
    [ intros; simpl; apply H
      | intros; simpl; apply H; apply RList_P1; assumption ].
Qed.

Lemma RList_P3 :
  forall (l:list R) (x:R),
    In x l <-> (exists i : nat, x = pos_Rl l i /\ (i < length l)%nat).
Proof.
  intros; split; intro;
    [ induction  l as [| r l Hrecl] | induction  l as [| r l Hrecl] ].
  - elim H.
  - elim H; intro;
      [ exists 0%nat; split; [ symmetry; apply H0 | simpl; apply Nat.lt_0_succ ]
        | elim (Hrecl H0); intros; elim H1; clear H1; intros; exists (S x0); split;
          [ apply H1 | simpl; apply -> Nat.succ_lt_mono; assumption ] ].
  - elim H; intros; elim H0; intros; elim (Nat.nlt_0_r _ H2).
  - simpl; elim H; intros; elim H0; clear H0; intros;
      induction  x0 as [| x0 Hrecx0];
      [ left; symmetry; apply H0
      | right; apply Hrecl; exists x0; split;
        [ apply H0 | simpl in H1; apply Nat.succ_lt_mono; assumption ] ].
Qed.

Lemma RList_P4 :
  forall (l1:list R) (a:R), ordered_Rlist (a :: l1) -> ordered_Rlist l1.
Proof.
  intros; unfold ordered_Rlist; intros; apply (H (S i)); simpl;
    replace (length l1) with (S (pred (length l1)));
    [ apply -> Nat.succ_lt_mono; assumption
      | apply Nat.lt_succ_pred with 0%nat; apply Nat.neq_0_lt_0; red;
        intro; rewrite H1 in H0; elim (Nat.nlt_0_r _ H0) ].
Qed.

Lemma RList_P5 :
  forall (l:list R) (x:R), ordered_Rlist l -> In x l -> pos_Rl l 0 <= x.
Proof.
  intros; induction  l as [| r l Hrecl];
    [ elim H0
      | simpl; elim H0; intro;
        [ rewrite H1; right; reflexivity
          | apply Rle_trans with (pos_Rl l 0);
            [ apply (H 0%nat); simpl; induction  l as [| r0 l Hrecl0];
              [ elim H1 | simpl; apply Nat.lt_0_succ ]
              | apply Hrecl; [ eapply RList_P4; apply H | assumption ] ] ] ].
Qed.

Lemma RList_P6 :
  forall l:list R,
    ordered_Rlist l <->
    (forall i j:nat,
      (i <= j)%nat -> (j < length l)%nat -> pos_Rl l i <= pos_Rl l j).
Proof.
  induction l as [ | r r0 H]; split; intro.
  - intros; right; reflexivity.
  - unfold ordered_Rlist;intros; simpl in H0; elim (Nat.nlt_0_r _ H0).
  - intros; induction i as [| i Hreci];
      [ induction j as [| j Hrecj];
        [ right; reflexivity
        | simpl; apply Rle_trans with (pos_Rl r0 0);
          [ apply (H0 0%nat); simpl; simpl in H2; apply Nat.neq_0_lt_0;
            red; intro; rewrite H3 in H2;
            assert (H4 := proj2 (Nat.succ_lt_mono _ _) H2); elim (Nat.nlt_0_r _ H4)
          | elim H; intros; apply H3;
            [ apply RList_P4 with r; assumption
            | apply Nat.le_0_l
            | simpl in H2; apply Nat.succ_lt_mono; assumption ] ] ]
      | induction j as [| j Hrecj];
        [ elim (Nat.nle_succ_0 _ H1)
        | simpl; elim H; intros; apply H3;
          [ apply RList_P4 with r; assumption
          | apply le_S_n; assumption
          | simpl in H2; apply Nat.succ_lt_mono; assumption ] ] ].
  - unfold ordered_Rlist; intros; apply H0;
      [ apply Nat.le_succ_diag_r | simpl; simpl in H1; apply -> Nat.succ_lt_mono; assumption ].
Qed.

Lemma RList_P7 :
  forall (l:list R) (x:R),
    ordered_Rlist l -> In x l -> x <= pos_Rl l (pred (length l)).
Proof.
  intros; assert (H1 := RList_P6 l); elim H1; intros H2 _; assert (H3 := H2 H);
    clear H1 H2; assert (H1 := RList_P3 l x); elim H1;
      clear H1; intros; assert (H4 := H1 H0); elim H4; clear H4;
        intros; elim H4; clear H4; intros; rewrite H4;
          assert (H6 : length l = S (pred (length l))).
  - symmetry; apply Nat.lt_succ_pred with 0%nat; apply Nat.neq_0_lt_0; red; intro;
      rewrite H6 in H5; elim (Nat.nlt_0_r _ H5).
  - apply H3;
      [ rewrite H6 in H5; apply Nat.lt_succ_r; assumption
      | apply Nat.lt_pred_l; red; intro; rewrite H7 in H5;
        elim (Nat.nlt_0_r _ H5) ].
Qed.

Lemma RList_P8 :
  forall (l:list R) (a x:R), In x (insert l a) <-> x = a \/ In x l.
Proof.
  induction l as [ | r r0 H].
  - intros; split; intro; destruct H as [ax | []]; left; symmetry; exact ax.
  - intros; split; intro.
    + simpl in H0; generalize H0; case (Rle_dec r a); intros.
      * simpl in H1; elim H1; intro.
        -- right; left; assumption.
        -- elim (H a x); intros; elim (H3 H2); intro.
           ++ left; assumption.
           ++ right; right; assumption.
      * simpl in H1; decompose [or] H1.
        -- left; symmetry; assumption.
        -- right; left; assumption.
        -- right; right; assumption.
    + simpl; case (Rle_dec r a); intro.
      * simpl in H0; decompose [or] H0.
        -- right; elim (H a x); intros; apply H3; left.  assumption.
        -- left. assumption.
        -- right; elim (H a x); intros; apply H3; right; assumption.
      * simpl in H0; decompose [or] H0; [ left | right; left | right; right];
          trivial; symmetry; assumption.
Qed.

Lemma RList_P9 :
  forall (l1 l2:list R) (x:R), In x (cons_ORlist l1 l2) <-> In x l1 \/ In x l2.
Proof.
  induction l1 as [ | r r0 H].
  - intros; split; intro;
      [ simpl in H; right; assumption
      | simpl; elim H; intro; [ elim H0 | assumption ] ].
  - intros; split.
    + simpl; intros; elim (H (insert l2 r) x); intros; assert (H3 := H1 H0);
        elim H3; intro.
      * left; right; assumption.
      * elim (RList_P8 l2 r x); intros H5 _; assert (H6 := H5 H4); elim H6; intro.
        -- left; left; symmetry; assumption.
        -- right; assumption.
    + intro; simpl; elim (H (insert l2 r) x); intros _ H1; apply H1;
        elim H0; intro.
      * elim H2; intro.
        -- right; elim (RList_P8 l2 r x); intros _ H4; apply H4; left.
           symmetry; assumption.
        -- left; assumption.
      * right; elim (RList_P8 l2 r x); intros _ H3; apply H3; right; assumption.
Qed.

Lemma RList_P10 :
  forall (l:list R) (a:R), length (insert l a) = S (length l).
Proof.
  intros; induction  l as [| r l Hrecl];
    [ reflexivity
      | simpl; case (Rle_dec r a); intro;
        [ simpl; rewrite Hrecl; reflexivity | reflexivity ] ].
Qed.

Lemma RList_P11 :
  forall l1 l2:list R,
    length (cons_ORlist l1 l2) = (length l1 + length l2)%nat.
Proof.
  induction l1 as [ | r r0 H];
    [ intro; reflexivity
      | intros; simpl; rewrite (H (insert l2 r)); rewrite RList_P10;
        apply INR_eq; rewrite S_INR; do 2 rewrite plus_INR;
          rewrite S_INR; ring ].
Qed.

Lemma RList_P12 :
  forall (l:list R) (i:nat) (f:R -> R),
    (i < length l)%nat -> pos_Rl (map f l) i = f (pos_Rl l i).
Proof.
  simple induction l;
    [ intros; elim (Nat.nlt_0_r _ H)
      | intros; induction  i as [| i Hreci];
        [ reflexivity | simpl; apply H; apply Nat.succ_lt_mono; apply H0 ] ].
Qed.

Lemma RList_P13 :
  forall (l:list R) (i:nat) (a:R),
    (i < pred (length l))%nat ->
    pos_Rl (mid_Rlist l a) (S i) = (pos_Rl l i + pos_Rl l (S i)) / 2.
Proof.
  induction l as [ | r r0 H].
  - intros; simpl in H; elim (Nat.nlt_0_r _ H).
  - induction r0 as [ | r1 r2 H0].
    + intros; simpl in H0; elim (Nat.nlt_0_r _ H0).
    + intros; simpl in H1; induction  i as [| i Hreci].
      * reflexivity.
      * change
          (pos_Rl (mid_Rlist (r1 :: r2) r) (S i) =
             (pos_Rl (r1 :: r2) i + pos_Rl (r1 :: r2) (S i)) / 2).
        apply H; simpl; apply Nat.succ_lt_mono; assumption.
Qed.

Lemma RList_P14 : forall (l:list R) (a:R), length (mid_Rlist l a) = length l.
Proof.
  induction l as [ | r r0 H]; intros;
    [ reflexivity | simpl; rewrite (H r); reflexivity ].
Qed.

Lemma RList_P15 :
  forall l1 l2:list R,
    ordered_Rlist l1 ->
    ordered_Rlist l2 ->
    pos_Rl l1 0 = pos_Rl l2 0 -> pos_Rl (cons_ORlist l1 l2) 0 = pos_Rl l1 0.
Proof.
  intros; apply Rle_antisym.
  - induction  l1 as [| r l1 Hrecl1];
      [ simpl; simpl in H1; right; symmetry ; assumption
      | elim (RList_P9 (r :: l1) l2 (pos_Rl (r :: l1) 0)); intros;
        assert
          (H4 :
            In (pos_Rl (r :: l1) 0) (r :: l1) \/ In (pos_Rl (r :: l1) 0) l2);
        [ left; left; reflexivity
        | assert (H5 := H3 H4); apply RList_P5;
          [ apply RList_P2; assumption | assumption ] ] ].
  - induction  l1 as [| r l1 Hrecl1];
      [ simpl; simpl in H1; right; assumption
      | assert
          (H2 :
            In (pos_Rl (cons_ORlist (r :: l1) l2) 0) (cons_ORlist (r :: l1) l2));
        [ elim
            (RList_P3 (cons_ORlist (r :: l1) l2)
                      (pos_Rl (cons_ORlist (r :: l1) l2) 0));
          intros; apply H3; exists 0%nat; split;
          [ reflexivity | rewrite RList_P11; simpl; apply Nat.lt_0_succ ]
        | elim (RList_P9 (r :: l1) l2 (pos_Rl (cons_ORlist (r :: l1) l2) 0));
          intros; assert (H5 := H3 H2); elim H5; intro;
          [ apply RList_P5; assumption
          | rewrite H1; apply RList_P5; assumption ] ] ].
Qed.

Lemma RList_P16 :
  forall l1 l2:list R,
    ordered_Rlist l1 ->
    ordered_Rlist l2 ->
    pos_Rl l1 (pred (length l1)) = pos_Rl l2 (pred (length l2)) ->
    pos_Rl (cons_ORlist l1 l2) (pred (length (cons_ORlist l1 l2))) =
    pos_Rl l1 (pred (length l1)).
Proof.
  intros; apply Rle_antisym.
  - induction  l1 as [| r l1 Hrecl1].
    + simpl; simpl in H1; right; symmetry ; assumption.
    + assert
        (H2 :
          In
            (pos_Rl (cons_ORlist (r :: l1) l2)
                    (pred (length (cons_ORlist (r :: l1) l2))))
            (cons_ORlist (r :: l1) l2));
        [ elim
            (RList_P3 (cons_ORlist (r :: l1) l2)
                      (pos_Rl (cons_ORlist (r :: l1) l2)
                              (pred (length (cons_ORlist (r :: l1) l2)))));
          intros; apply H3; exists (pred (length (cons_ORlist (r :: l1) l2)));
          split; [ reflexivity | rewrite RList_P11; simpl; apply Nat.lt_succ_diag_r ]
        | elim
            (RList_P9 (r :: l1) l2
                      (pos_Rl (cons_ORlist (r :: l1) l2)
                              (pred (length (cons_ORlist (r :: l1) l2)))));
          intros; assert (H5 := H3 H2); elim H5; intro;
          [ apply RList_P7; assumption | rewrite H1; apply RList_P7; assumption ] ].
  - induction  l1 as [| r l1 Hrecl1].
    + simpl; simpl in H1; right; assumption.
    + elim
        (RList_P9 (r :: l1) l2 (pos_Rl (r :: l1) (pred (length (r :: l1))))).
      intros;
        assert
          (H4 :
            In (pos_Rl (r :: l1) (pred (length (r :: l1)))) (r :: l1) \/
              In (pos_Rl (r :: l1) (pred (length (r :: l1)))) l2);
        [ left; change (In (pos_Rl (r :: l1) (length l1)) (r :: l1));
          elim (RList_P3 (r :: l1) (pos_Rl (r :: l1) (length l1)));
          intros; apply H5; exists (length l1); split;
          [ reflexivity | simpl; apply Nat.lt_succ_diag_r ]
        | assert (H5 := H3 H4); apply RList_P7;
          [ apply RList_P2; assumption
          | elim
              (RList_P9 (r :: l1) l2
                        (pos_Rl (r :: l1) (pred (length (r :: l1)))));
            intros; apply H7; left;
            elim
              (RList_P3 (r :: l1)
                        (pos_Rl (r :: l1) (pred (length (r :: l1)))));
            intros; apply H9; exists (pred (length (r :: l1)));
            split; [ reflexivity | simpl; apply Nat.lt_succ_diag_r ] ] ].
Qed.

Lemma RList_P17 :
  forall (l1:list R) (x:R) (i:nat),
    ordered_Rlist l1 ->
    In x l1 ->
    pos_Rl l1 i < x -> (i < pred (length l1))%nat -> pos_Rl l1 (S i) <= x.
Proof.
  induction l1 as [ | r r0 H].
  - intros; elim H0.
  - intros; induction  i as [| i Hreci].
    + simpl; elim H1; intro;
        [ simpl in H2; rewrite H4 in H2; elim (Rlt_irrefl _ H2)
        | apply RList_P5; [ apply RList_P4 with r; assumption | assumption ] ].
    + simpl; simpl in H2; elim H1; intro.
      * rewrite <- H4 in H2; assert (H5 : r <= pos_Rl r0 i);
          [ apply Rle_trans with (pos_Rl r0 0);
            [ apply (H0 0%nat); simpl; simpl in H3; apply Nat.neq_0_lt_0;
              red; intro; rewrite H5 in H3; elim (Nat.nlt_0_r _ H3)
            | elim (RList_P6 r0); intros; apply H5;
              [ apply RList_P4 with r; assumption
              | apply Nat.le_0_l
              | simpl in H3; apply Nat.succ_lt_mono; apply Nat.lt_trans with (length r0);
                [ apply H3 | apply Nat.lt_succ_diag_r ] ] ]
          | elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H5 H2)) ].
      * apply H; try assumption;
          [ apply RList_P4 with r; assumption
          | simpl in H3; apply Nat.succ_lt_mono;
            replace (S (pred (length r0))) with (length r0);
            [ apply H3
            | symmetry; apply Nat.lt_succ_pred with 0%nat; apply Nat.neq_0_lt_0; red; intro;
              rewrite H5 in H3; elim (Nat.nlt_0_r _ H3) ] ].
Qed.

Lemma RList_P18 :
  forall (l:list R) (f:R -> R), length (map f l) = length l.
Proof.
  simple induction l; intros;
    [ reflexivity | simpl; rewrite H; reflexivity ].
Qed.

Lemma RList_P19 :
  forall l:list R,
    l <> nil ->  exists r : R, (exists r0 : list R, l = r :: r0).
Proof.
  intros; induction  l as [| r l Hrecl];
    [ elim H; reflexivity | exists r; exists l; reflexivity ].
Qed.

Lemma RList_P20 :
  forall l:list R,
    (2 <= length l)%nat ->
    exists r : R,
      (exists r1 : R, (exists l' : list R, l = r :: r1 :: l')).
Proof.
  intros; induction  l as [| r l Hrecl];
    [ simpl in H; elim (Nat.nle_succ_0 _ H)
      | induction  l as [| r0 l Hrecl0];
        [ simpl in H; elim (Nat.nle_succ_0 _ (le_S_n _ _ H))
          | exists r; exists r0; exists l; reflexivity ] ].
Qed.

Lemma RList_P21 : forall l l':list R, l = l' -> Rtail l = Rtail l'.
Proof.
  intros; rewrite H; reflexivity.
Qed.

Lemma RList_P22 :
  forall l1 l2:list R, l1 <> nil -> pos_Rl (app l1 l2) 0 = pos_Rl l1 0.
Proof.
  simple induction l1; [ intros; elim H; reflexivity | intros; reflexivity ].
Qed.

Lemma RList_P24 :
  forall l1 l2:list R,
    l2 <> nil ->
    pos_Rl (app l1 l2) (pred (length (app l1 l2))) =
    pos_Rl l2 (pred (length l2)).
Proof.
  induction l1 as [ | r r0 H].
  - intros; reflexivity.
  - intros; rewrite <- (H l2 H0); induction  l2 as [| r1 l2 Hrecl2].
    + elim H0; reflexivity.
    + do 2 rewrite length_app;
      replace (length (r :: r0) + length (r1 :: l2))%nat with
        (S (S (length r0 + length l2)));
      [ replace (length r0 + length (r1 :: l2))%nat with
        (S (length r0 + length l2));
        [ reflexivity
        | simpl; apply INR_eq; rewrite S_INR; do 2 rewrite plus_INR;
          rewrite S_INR; ring ]
      | simpl; apply INR_eq; do 3 rewrite S_INR; do 2 rewrite plus_INR;
        rewrite S_INR; ring ].
Qed.

Lemma RList_P25 :
  forall l1 l2:list R,
    ordered_Rlist l1 ->
    ordered_Rlist l2 ->
    pos_Rl l1 (pred (length l1)) <= pos_Rl l2 0 ->
    ordered_Rlist (app l1 l2).
Proof.
  induction l1 as [ | r r0 H].
  - intros; simpl; assumption.
  - induction r0 as [ | r1 r2 H0].
    + intros; simpl; simpl in H2; unfold ordered_Rlist; intros;
        simpl in H3.
      induction  i as [| i Hreci].
      * simpl; assumption.
      * change (pos_Rl l2 i <= pos_Rl l2 (S i)); apply (H1 i); apply Nat.succ_lt_mono;
          replace (S (pred (length l2))) with (length l2);
          [ assumption
          | symmetry; apply Nat.lt_succ_pred with 0%nat; apply Nat.neq_0_lt_0; red; intro;
            rewrite H4 in H3; elim (Nat.nlt_0_r _ H3) ].
    + intros; assert (H4 : ordered_Rlist (app (r1 :: r2) l2)).
      * apply H; try assumption.
        apply RList_P4 with r; assumption.
      * unfold ordered_Rlist; intros i H5; simpl in H5.
        induction  i as [| i Hreci].
        -- simpl; apply (H1 0%nat); simpl; apply Nat.lt_0_succ.
        -- change
            (pos_Rl (app (r1 :: r2) l2) i <=
               pos_Rl (app (r1 :: r2) l2) (S i));
            apply (H4 i); simpl; apply Nat.succ_lt_mono; assumption.
Qed.

Lemma RList_P26 :
  forall (l1 l2:list R) (i:nat),
    (i < length l1)%nat -> pos_Rl (app l1 l2) i = pos_Rl l1 i.
Proof.
  simple induction l1.
  - intros; elim (Nat.nlt_0_r _ H).
  - intros; induction  i as [| i Hreci].
    + apply RList_P22; discriminate.
    + apply (H l2 i); simpl in H0; apply Nat.succ_lt_mono; assumption.
Qed.

Lemma RList_P29 :
  forall (l2 l1:list R) (i:nat),
    (length l1 <= i)%nat ->
    (i < length (app l1 l2))%nat ->
    pos_Rl (app l1 l2) i = pos_Rl l2 (i - length l1).
Proof.
  induction l2 as [ | r r0 H].
  - intros; rewrite app_nil_r in H0; elim (Nat.lt_irrefl _ (Nat.le_lt_trans _ _ _ H H0)).
  - intros;
      replace (app l1 (r :: r0)) with
      (app (app l1 (r :: nil)) r0).
    + inversion H0.
      * rewrite Nat.sub_diag; simpl; rewrite RList_P26.
        -- clear r0 H i H0 H1 H2; induction  l1 as [| r0 l1 Hrecl1].
           ++ reflexivity.
           ++ simpl; assumption.
        -- rewrite length_app; rewrite Nat.add_comm; simpl; apply Nat.lt_succ_diag_r.
      * replace (S m - length l1)%nat with (S (S m - S (length l1))).
        -- rewrite H3; simpl;
             replace (S (length l1)) with (length (app l1 (r :: nil))).
           ++ apply (H (app l1 (r :: nil)) i).
              ** rewrite length_app; rewrite Nat.add_comm; simpl; rewrite <- H3;
                   apply le_n_S; assumption.
              ** repeat rewrite length_app; simpl; rewrite length_app in H1;
                   rewrite Nat.add_comm in H1; simpl in H1; rewrite (Nat.add_comm (length l1));
                   simpl; rewrite Nat.add_comm; apply H1.
           ++ rewrite length_app; rewrite Nat.add_comm; reflexivity.
        -- change (S (m - length l1) = (S m - length l1)%nat);
             symmetry; apply Nat.sub_succ_l; assumption.
    + replace (r :: r0) with (app (r :: nil) r0);
        [ symmetry ; apply app_assoc | reflexivity ].
Qed.

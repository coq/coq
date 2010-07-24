(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Rbase.
Require Import Rfunctions.
Require Import Ranalysis.
Require Import Classical_Prop.
Open Local Scope R_scope.

Set Implicit Arguments.

(*****************************************************)
(** * Each bounded subset of N has a maximal element *)
(*****************************************************)

Definition Nbound (I:nat -> Prop) : Prop :=
  exists n : nat, (forall i:nat, I i -> (i <= n)%nat).

Lemma IZN_var : forall z:Z, (0 <= z)%Z -> {n : nat | z = Z_of_nat n}.
Proof.
  intros; apply Z_of_nat_complete_inf; assumption.
Qed.

Lemma Nzorn :
  forall I:nat -> Prop,
    (exists n : nat, I n) ->
    Nbound I -> { n:nat | I n /\ (forall i:nat, I i -> (i <= n)%nat) }.
Proof.
  intros I H H0; set (E := fun x:R =>  exists i : nat, I i /\ INR i = x);
    assert (H1 : bound E).
  unfold Nbound in H0; elim H0; intros N H1; unfold bound in |- *;
    exists (INR N); unfold is_upper_bound in |- *; intros;
      unfold E in H2; elim H2; intros; elim H3; intros;
        rewrite <- H5; apply le_INR; apply H1; assumption.
  assert (H2 :  exists x : R, E x).
  elim H; intros; exists (INR x); unfold E in |- *; exists x; split;
    [ assumption | reflexivity ].
  assert (H3 := completeness E H1 H2); elim H3; intros; unfold is_lub in p;
    elim p; clear p; intros; unfold is_upper_bound in H4, H5;
      assert (H6 : 0 <= x).
  elim H2; intros; unfold E in H6; elim H6; intros; elim H7; intros;
    apply Rle_trans with x0;
      [ rewrite <- H9; change (INR 0 <= INR x1) in |- *; apply le_INR;
        apply le_O_n
        | apply H4; assumption ].
  assert (H7 := archimed x); elim H7; clear H7; intros;
    assert (H9 : x <= IZR (up x) - 1).
  apply H5; intros; assert (H10 := H4 _ H9); unfold E in H9; elim H9; intros;
    elim H11; intros; rewrite <- H13; apply Rplus_le_reg_l with 1;
      replace (1 + (IZR (up x) - 1)) with (IZR (up x));
      [ idtac | ring ]; replace (1 + INR x1) with (INR (S x1));
      [ idtac | rewrite S_INR; ring ].
  assert (H14 : (0 <= up x)%Z).
  apply le_IZR; apply Rle_trans with x; [ apply H6 | left; assumption ].
  assert (H15 := IZN _ H14); elim H15; clear H15; intros; rewrite H15;
    rewrite <- INR_IZR_INZ; apply le_INR; apply lt_le_S;
      apply INR_lt; rewrite H13; apply Rle_lt_trans with x;
        [ assumption | rewrite INR_IZR_INZ; rewrite <- H15; assumption ].
  assert (H10 : x = IZR (up x) - 1).
  apply Rle_antisym;
    [ assumption
      | apply Rplus_le_reg_l with (- x + 1);
        replace (- x + 1 + (IZR (up x) - 1)) with (IZR (up x) - x);
        [ idtac | ring ]; replace (- x + 1 + x) with 1;
        [ assumption | ring ] ].
  assert (H11 : (0 <= up x)%Z).
  apply le_IZR; apply Rle_trans with x; [ apply H6 | left; assumption ].
  assert (H12 := IZN_var H11); elim H12; clear H12; intros; assert (H13 : E x).
  elim (classic (E x)); intro; try assumption.
  cut (forall y:R, E y -> y <= x - 1).
  intro; assert (H14 := H5 _ H13); cut (x - 1 < x).
  intro; elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H14 H15)).
  apply Rminus_lt; replace (x - 1 - x) with (-1); [ idtac | ring ];
    rewrite <- Ropp_0; apply Ropp_lt_gt_contravar; apply Rlt_0_1.
  intros; assert (H14 := H4 _ H13); elim H14; intro; unfold E in H13; elim H13;
    intros; elim H16; intros; apply Rplus_le_reg_l with 1.
  replace (1 + (x - 1)) with x; [ idtac | ring ]; rewrite <- H18;
    replace (1 + INR x1) with (INR (S x1)); [ idtac | rewrite S_INR; ring ].
  cut (x = INR (pred x0)).
  intro; rewrite H19; apply le_INR; apply lt_le_S; apply INR_lt; rewrite H18;
    rewrite <- H19; assumption.
  rewrite H10; rewrite p; rewrite <- INR_IZR_INZ; replace 1 with (INR 1);
    [ idtac | reflexivity ]; rewrite <- minus_INR.
  replace (x0 - 1)%nat with (pred x0);
  [ reflexivity
    | case x0; [ reflexivity | intro; simpl in |- *; apply minus_n_O ] ].
  induction  x0 as [| x0 Hrecx0];
    [ rewrite p in H7; rewrite <- INR_IZR_INZ in H7; simpl in H7;
      elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H6 H7))
      | apply le_n_S; apply le_O_n ].
  rewrite H15 in H13; elim H12; assumption.
  split with (pred x0); unfold E in H13; elim H13; intros; elim H12; intros;
    rewrite H10 in H15; rewrite p in H15; rewrite <- INR_IZR_INZ in H15;
      assert (H16 : INR x0 = INR x1 + 1).
  rewrite H15; ring.
  rewrite <- S_INR in H16; assert (H17 := INR_eq _ _ H16); rewrite H17;
    simpl in |- *; split.
  assumption.
  intros; apply INR_le; rewrite H15; rewrite <- H15; elim H12; intros;
    rewrite H20; apply H4; unfold E in |- *; exists i;
      split; [ assumption | reflexivity ].
Qed.

(*******************************************)
(** *          Step functions              *)
(*******************************************)

Definition open_interval (a b x:R) : Prop := a < x < b.
Definition co_interval (a b x:R) : Prop := a <= x < b.

Definition adapted_couple (f:R -> R) (a b:R) (l lf:Rlist) : Prop :=
  ordered_Rlist l /\
  pos_Rl l 0 = Rmin a b /\
  pos_Rl l (pred (Rlength l)) = Rmax a b /\
  Rlength l = S (Rlength lf) /\
  (forall i:nat,
    (i < pred (Rlength l))%nat ->
    constant_D_eq f (open_interval (pos_Rl l i) (pos_Rl l (S i)))
    (pos_Rl lf i)).

Definition adapted_couple_opt (f:R -> R) (a b:R) (l lf:Rlist) :=
  adapted_couple f a b l lf /\
  (forall i:nat,
    (i < pred (Rlength lf))%nat ->
    pos_Rl lf i <> pos_Rl lf (S i) \/ f (pos_Rl l (S i)) <> pos_Rl lf i) /\
  (forall i:nat, (i < pred (Rlength l))%nat -> pos_Rl l i <> pos_Rl l (S i)).

Definition is_subdivision (f:R -> R) (a b:R) (l:Rlist) : Type :=
  { l0:Rlist & adapted_couple f a b l l0 }.

Definition IsStepFun (f:R -> R) (a b:R) : Type :=
  { l:Rlist & is_subdivision f a b l }.

(** ** Class of step functions *)
Record StepFun (a b:R) : Type := mkStepFun
  {fe :> R -> R; pre : IsStepFun fe a b}.

Definition subdivision (a b:R) (f:StepFun a b) : Rlist := projT1 (pre f).

Definition subdivision_val (a b:R) (f:StepFun a b) : Rlist :=
  match projT2 (pre f) with
    | existT a b => a
  end.

Boxed Fixpoint Int_SF (l k:Rlist) : R :=
  match l with
    | nil => 0
    | cons a l' =>
      match k with
        | nil => 0
        | cons x nil => 0
        | cons x (cons y k') => a * (y - x) + Int_SF l' (cons y k')
      end
  end.

(** ** Integral of step functions *)
Definition RiemannInt_SF (a b:R) (f:StepFun a b) : R :=
  match Rle_dec a b with
    | left _ => Int_SF (subdivision_val f) (subdivision f)
    | right _ => - Int_SF (subdivision_val f) (subdivision f)
  end.

(************************************)
(** ** Properties of step functions *)
(************************************)

Lemma StepFun_P1 :
  forall (a b:R) (f:StepFun a b),
    adapted_couple f a b (subdivision f) (subdivision_val f).
Proof.
  intros a b f; unfold subdivision_val in |- *; case (projT2 (pre f)); intros;
    apply a0.
Qed.

Lemma StepFun_P2 :
  forall (a b:R) (f:R -> R) (l lf:Rlist),
    adapted_couple f a b l lf -> adapted_couple f b a l lf.
Proof.
  unfold adapted_couple in |- *; intros; decompose [and] H; clear H;
    repeat split; try assumption.
  rewrite H2; unfold Rmin in |- *; case (Rle_dec a b); intro;
    case (Rle_dec b a); intro; try reflexivity.
  apply Rle_antisym; assumption.
  apply Rle_antisym; auto with real.
  rewrite H1; unfold Rmax in |- *; case (Rle_dec a b); intro;
    case (Rle_dec b a); intro; try reflexivity.
  apply Rle_antisym; assumption.
  apply Rle_antisym; auto with real.
Qed.

Lemma StepFun_P3 :
  forall a b c:R,
    a <= b ->
    adapted_couple (fct_cte c) a b (cons a (cons b nil)) (cons c nil).
Proof.
  intros; unfold adapted_couple in |- *; repeat split.
  unfold ordered_Rlist in |- *; intros; simpl in H0; inversion H0;
    [ simpl in |- *; assumption | elim (le_Sn_O _ H2) ].
  simpl in |- *; unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; assumption ].
  simpl in |- *; unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; assumption ].
  unfold constant_D_eq, open_interval in |- *; intros; simpl in H0;
    inversion H0; [ reflexivity | elim (le_Sn_O _ H3) ].
Qed.

Lemma StepFun_P4 : forall a b c:R, IsStepFun (fct_cte c) a b.
Proof.
  intros; unfold IsStepFun in |- *; case (Rle_dec a b); intro.
  apply existT with (cons a (cons b nil)); unfold is_subdivision in |- *;
    apply existT with (cons c nil); apply (StepFun_P3 c r).
  apply existT with (cons b (cons a nil)); unfold is_subdivision in |- *;
    apply existT with (cons c nil); apply StepFun_P2;
      apply StepFun_P3; auto with real.
Qed.

Lemma StepFun_P5 :
  forall (a b:R) (f:R -> R) (l:Rlist),
    is_subdivision f a b l -> is_subdivision f b a l.
Proof.
  destruct 1 as (x,(H0,(H1,(H2,(H3,H4))))); exists x;
    repeat split; try assumption.
  rewrite H1; apply Rmin_comm.
  rewrite H2; apply Rmax_comm.
Qed.

Lemma StepFun_P6 :
  forall (f:R -> R) (a b:R), IsStepFun f a b -> IsStepFun f b a.
Proof.
  unfold IsStepFun in |- *; intros; elim X; intros; apply existT with x;
    apply StepFun_P5; assumption.
Qed.

Lemma StepFun_P7 :
  forall (a b r1 r2 r3:R) (f:R -> R) (l lf:Rlist),
    a <= b ->
    adapted_couple f a b (cons r1 (cons r2 l)) (cons r3 lf) ->
    adapted_couple f r2 b (cons r2 l) lf.
Proof.
  unfold adapted_couple in |- *; intros; decompose [and] H0; clear H0;
    assert (H5 : Rmax a b = b).
  unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; assumption ].
  assert (H7 : r2 <= b).
  rewrite H5 in H2; rewrite <- H2; apply RList_P7;
    [ assumption | simpl in |- *; right; left; reflexivity ].
  repeat split.
  apply RList_P4 with r1; assumption.
  rewrite H5 in H2; unfold Rmin in |- *; case (Rle_dec r2 b); intro;
    [ reflexivity | elim n; assumption ].
  unfold Rmax in |- *; case (Rle_dec r2 b); intro;
    [ rewrite H5 in H2; rewrite <- H2; reflexivity | elim n; assumption ].
  simpl in H4; simpl in |- *; apply INR_eq; apply Rplus_eq_reg_l with 1;
    do 2 rewrite (Rplus_comm 1); do 2 rewrite <- S_INR;
      rewrite H4; reflexivity.
  intros; unfold constant_D_eq, open_interval in |- *; intros;
    unfold constant_D_eq, open_interval in H6;
      assert (H9 : (S i < pred (Rlength (cons r1 (cons r2 l))))%nat).
  simpl in |- *; simpl in H0; apply lt_n_S; assumption.
  assert (H10 := H6 _ H9); apply H10; assumption.
Qed.

Lemma StepFun_P8 :
  forall (f:R -> R) (l1 lf1:Rlist) (a b:R),
    adapted_couple f a b l1 lf1 -> a = b -> Int_SF lf1 l1 = 0.
Proof.
  simple induction l1.
  intros; induction  lf1 as [| r lf1 Hreclf1]; reflexivity.
  simple induction r0.
  intros; induction  lf1 as [| r1 lf1 Hreclf1].
  reflexivity.
  unfold adapted_couple in H0; decompose [and] H0; clear H0; simpl in H5;
    discriminate.
  intros; induction  lf1 as [| r3 lf1 Hreclf1].
  reflexivity.
  simpl in |- *; cut (r = r1).
  intro; rewrite H3; rewrite (H0 lf1 r b).
  ring.
  rewrite H3; apply StepFun_P7 with a r r3; [ right; assumption | assumption ].
  clear H H0 Hreclf1 r0; unfold adapted_couple in H1; decompose [and] H1;
    intros; simpl in H4; rewrite H4; unfold Rmin in |- *;
      case (Rle_dec a b); intro; [ assumption | reflexivity ].
  unfold adapted_couple in H1; decompose [and] H1; intros; apply Rle_antisym.
  apply (H3 0%nat); simpl in |- *; apply lt_O_Sn.
  simpl in H5; rewrite H2 in H5; rewrite H5; replace (Rmin b b) with (Rmax a b);
    [ rewrite <- H4; apply RList_P7;
      [ assumption | simpl in |- *; right; left; reflexivity ]
      | unfold Rmin, Rmax in |- *; case (Rle_dec b b); case (Rle_dec a b); intros;
        try assumption || reflexivity ].
Qed.

Lemma StepFun_P9 :
  forall (a b:R) (f:R -> R) (l lf:Rlist),
    adapted_couple f a b l lf -> a <> b -> (2 <= Rlength l)%nat.
Proof.
  intros; unfold adapted_couple in H; decompose [and] H; clear H;
    induction  l as [| r l Hrecl];
      [ simpl in H4; discriminate
        | induction  l as [| r0 l Hrecl0];
          [ simpl in H3; simpl in H2; generalize H3; generalize H2;
            unfold Rmin, Rmax in |- *; case (Rle_dec a b);
              intros; elim H0; rewrite <- H5; rewrite <- H7;
                reflexivity
            | simpl in |- *; do 2 apply le_n_S; apply le_O_n ] ].
Qed.

Lemma StepFun_P10 :
  forall (f:R -> R) (l lf:Rlist) (a b:R),
    a <= b ->
    adapted_couple f a b l lf ->
    exists l' : Rlist,
      (exists lf' : Rlist, adapted_couple_opt f a b l' lf').
Proof.
  simple induction l.
  intros; unfold adapted_couple in H0; decompose [and] H0; simpl in H4;
    discriminate.
  intros; case (Req_dec a b); intro.
  exists (cons a nil); exists nil; unfold adapted_couple_opt in |- *;
    unfold adapted_couple in |- *; unfold ordered_Rlist in |- *;
      repeat split; try (intros; simpl in H3; elim (lt_n_O _ H3)).
  simpl in |- *; rewrite <- H2; unfold Rmin in |- *; case (Rle_dec a a); intro;
    reflexivity.
  simpl in |- *; rewrite <- H2; unfold Rmax in |- *; case (Rle_dec a a); intro;
    reflexivity.
  elim (RList_P20 _ (StepFun_P9 H1 H2)); intros t1 [t2 [t3 H3]];
    induction  lf as [| r1 lf Hreclf].
  unfold adapted_couple in H1; decompose [and] H1; rewrite H3 in H7;
    simpl in H7; discriminate.
  clear Hreclf; assert (H4 : adapted_couple f t2 b r0 lf).
  rewrite H3 in H1; assert (H4 := RList_P21 _ _ H3); simpl in H4; rewrite H4;
    eapply StepFun_P7; [ apply H0 | apply H1 ].
  cut (t2 <= b).
  intro; assert (H6 := H _ _ _ H5 H4); case (Req_dec t1 t2); intro Hyp_eq.
  replace a with t2.
  apply H6.
  rewrite <- Hyp_eq; rewrite H3 in H1; unfold adapted_couple in H1;
    decompose [and] H1; clear H1; simpl in H9; rewrite H9;
      unfold Rmin in |- *; case (Rle_dec a b); intro;
        [ reflexivity | elim n; assumption ].
  elim H6; clear H6; intros l' [lf' H6]; case (Req_dec t2 b); intro.
  exists (cons a (cons b nil)); exists (cons r1 nil);
    unfold adapted_couple_opt in |- *; unfold adapted_couple in |- *;
      repeat split.
  unfold ordered_Rlist in |- *; intros; simpl in H8; inversion H8;
    [ simpl in |- *; assumption | elim (le_Sn_O _ H10) ].
  simpl in |- *; unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; assumption ].
  simpl in |- *; unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; assumption ].
  intros; simpl in H8; inversion H8.
  unfold constant_D_eq, open_interval in |- *; intros; simpl in |- *;
    simpl in H9; rewrite H3 in H1; unfold adapted_couple in H1;
      decompose [and] H1; apply (H16 0%nat).
  simpl in |- *; apply lt_O_Sn.
  unfold open_interval in |- *; simpl in |- *; rewrite H7; simpl in H13;
    rewrite H13; unfold Rmin in |- *; case (Rle_dec a b);
      intro; [ assumption | elim n; assumption ].
  elim (le_Sn_O _ H10).
  intros; simpl in H8; elim (lt_n_O _ H8).
  intros; simpl in H8; inversion H8;
    [ simpl in |- *; assumption | elim (le_Sn_O _ H10) ].
  assert (Hyp_min : Rmin t2 b = t2).
  unfold Rmin in |- *; case (Rle_dec t2 b); intro;
    [ reflexivity | elim n; assumption ].
  unfold adapted_couple in H6; elim H6; clear H6; intros;
    elim (RList_P20 _ (StepFun_P9 H6 H7)); intros s1 [s2 [s3 H9]];
      induction  lf' as [| r2 lf' Hreclf'].
  unfold adapted_couple in H6; decompose [and] H6; rewrite H9 in H13;
    simpl in H13; discriminate.
  clear Hreclf'; case (Req_dec r1 r2); intro.
  case (Req_dec (f t2) r1); intro.
  exists (cons t1 (cons s2 s3)); exists (cons r1 lf'); rewrite H3 in H1;
    rewrite H9 in H6; unfold adapted_couple in H6, H1;
      decompose [and] H1; decompose [and] H6; clear H1 H6;
        unfold adapted_couple_opt in |- *; unfold adapted_couple in |- *;
          repeat split.
  unfold ordered_Rlist in |- *; intros; simpl in H1;
    induction  i as [| i Hreci].
  simpl in |- *; apply Rle_trans with s1.
  replace s1 with t2.
  apply (H12 0%nat).
  simpl in |- *; apply lt_O_Sn.
  simpl in H19; rewrite H19; symmetry  in |- *; apply Hyp_min.
  apply (H16 0%nat); simpl in |- *; apply lt_O_Sn.
  change (pos_Rl (cons s2 s3) i <= pos_Rl (cons s2 s3) (S i)) in |- *;
    apply (H16 (S i)); simpl in |- *; assumption.
  simpl in |- *; simpl in H14; rewrite H14; reflexivity.
  simpl in |- *; simpl in H18; rewrite H18; unfold Rmax in |- *;
    case (Rle_dec a b); case (Rle_dec t2 b); intros; reflexivity || elim n;
      assumption.
  simpl in |- *; simpl in H20; apply H20.
  intros; simpl in H1; unfold constant_D_eq, open_interval in |- *; intros;
    induction  i as [| i Hreci].
  simpl in |- *; simpl in H6; case (total_order_T x t2); intro.
  elim s; intro.
  apply (H17 0%nat);
    [ simpl in |- *; apply lt_O_Sn
      | unfold open_interval in |- *; simpl in |- *; elim H6; intros; split;
        assumption ].
  rewrite b0; assumption.
  rewrite H10; apply (H22 0%nat);
    [ simpl in |- *; apply lt_O_Sn
      | unfold open_interval in |- *; simpl in |- *; replace s1 with t2;
        [ elim H6; intros; split; assumption
          | simpl in H19; rewrite H19; rewrite Hyp_min; reflexivity ] ].
  simpl in |- *; simpl in H6; apply (H22 (S i));
    [ simpl in |- *; assumption
      | unfold open_interval in |- *; simpl in |- *; apply H6 ].
  intros; simpl in H1; rewrite H10;
    change
      (pos_Rl (cons r2 lf') i <> pos_Rl (cons r2 lf') (S i) \/
        f (pos_Rl (cons s1 (cons s2 s3)) (S i)) <> pos_Rl (cons r2 lf') i)
      in |- *; rewrite <- H9; elim H8; intros; apply H6;
        simpl in |- *; apply H1.
  intros; induction  i as [| i Hreci].
  simpl in |- *; red in |- *; intro; elim Hyp_eq; apply Rle_antisym.
  apply (H12 0%nat); simpl in |- *; apply lt_O_Sn.
  rewrite <- Hyp_min; rewrite H6; simpl in H19; rewrite <- H19;
    apply (H16 0%nat); simpl in |- *; apply lt_O_Sn.
  elim H8; intros; rewrite H9 in H21; apply (H21 (S i)); simpl in |- *;
    simpl in H1; apply H1.
  exists (cons t1 l'); exists (cons r1 (cons r2 lf')); rewrite H9 in H6;
    rewrite H3 in H1; unfold adapted_couple in H1, H6;
      decompose [and] H6; decompose [and] H1; clear H6 H1;
        unfold adapted_couple_opt in |- *; unfold adapted_couple in |- *;
          repeat split.
  rewrite H9; unfold ordered_Rlist in |- *; intros; simpl in H1;
    induction  i as [| i Hreci].
  simpl in |- *; replace s1 with t2.
  apply (H16 0%nat); simpl in |- *; apply lt_O_Sn.
  simpl in H14; rewrite H14; rewrite Hyp_min; reflexivity.
  change
    (pos_Rl (cons s1 (cons s2 s3)) i <= pos_Rl (cons s1 (cons s2 s3)) (S i))
    in |- *; apply (H12 i); simpl in |- *; apply lt_S_n;
      assumption.
  simpl in |- *; simpl in H19; apply H19.
  rewrite H9; simpl in |- *; simpl in H13; rewrite H13; unfold Rmax in |- *;
    case (Rle_dec t2 b); case (Rle_dec a b); intros; reflexivity || elim n;
      assumption.
  rewrite H9; simpl in |- *; simpl in H15; rewrite H15; reflexivity.
  intros; simpl in H1; unfold constant_D_eq, open_interval in |- *; intros;
    induction  i as [| i Hreci].
  simpl in |- *; rewrite H9 in H6; simpl in H6; apply (H22 0%nat).
  simpl in |- *; apply lt_O_Sn.
  unfold open_interval in |- *; simpl in |- *.
  replace t2 with s1.
  assumption.
  simpl in H14; rewrite H14; rewrite Hyp_min; reflexivity.
  change (f x = pos_Rl (cons r2 lf') i) in |- *; clear Hreci; apply (H17 i).
  simpl in |- *; rewrite H9 in H1; simpl in H1; apply lt_S_n; apply H1.
  rewrite H9 in H6; unfold open_interval in |- *; apply H6.
  intros; simpl in H1; induction  i as [| i Hreci].
  simpl in |- *; rewrite H9; right; simpl in |- *; replace s1 with t2.
  assumption.
  simpl in H14; rewrite H14; rewrite Hyp_min; reflexivity.
  elim H8; intros; apply (H6 i).
  simpl in |- *; apply lt_S_n; apply H1.
  intros; rewrite H9; induction  i as [| i Hreci].
  simpl in |- *; red in |- *; intro; elim Hyp_eq; apply Rle_antisym.
  apply (H16 0%nat); simpl in |- *; apply lt_O_Sn.
  rewrite <- Hyp_min; rewrite H6; simpl in H14; rewrite <- H14; right;
    reflexivity.
  elim H8; intros; rewrite <- H9; apply (H21 i); rewrite H9; rewrite H9 in H1;
    simpl in |- *; simpl in H1; apply lt_S_n; apply H1.
  exists (cons t1 l'); exists (cons r1 (cons r2 lf')); rewrite H9 in H6;
    rewrite H3 in H1; unfold adapted_couple in H1, H6;
      decompose [and] H6; decompose [and] H1; clear H6 H1;
        unfold adapted_couple_opt in |- *; unfold adapted_couple in |- *;
          repeat split.
  rewrite H9; unfold ordered_Rlist in |- *; intros; simpl in H1;
    induction  i as [| i Hreci].
  simpl in |- *; replace s1 with t2.
  apply (H15 0%nat); simpl in |- *; apply lt_O_Sn.
  simpl in H13; rewrite H13; rewrite Hyp_min; reflexivity.
  change
    (pos_Rl (cons s1 (cons s2 s3)) i <= pos_Rl (cons s1 (cons s2 s3)) (S i))
    in |- *; apply (H11 i); simpl in |- *; apply lt_S_n;
      assumption.
  simpl in |- *; simpl in H18; apply H18.
  rewrite H9; simpl in |- *; simpl in H12; rewrite H12; unfold Rmax in |- *;
    case (Rle_dec t2 b); case (Rle_dec a b); intros; reflexivity || elim n;
      assumption.
  rewrite H9; simpl in |- *; simpl in H14; rewrite H14; reflexivity.
  intros; simpl in H1; unfold constant_D_eq, open_interval in |- *; intros;
    induction  i as [| i Hreci].
  simpl in |- *; rewrite H9 in H6; simpl in H6; apply (H21 0%nat).
  simpl in |- *; apply lt_O_Sn.
  unfold open_interval in |- *; simpl in |- *; replace t2 with s1.
  assumption.
  simpl in H13; rewrite H13; rewrite Hyp_min; reflexivity.
  change (f x = pos_Rl (cons r2 lf') i) in |- *; clear Hreci; apply (H16 i).
  simpl in |- *; rewrite H9 in H1; simpl in H1; apply lt_S_n; apply H1.
  rewrite H9 in H6; unfold open_interval in |- *; apply H6.
  intros; simpl in H1; induction  i as [| i Hreci].
  simpl in |- *; left; assumption.
  elim H8; intros; apply (H6 i).
  simpl in |- *; apply lt_S_n; apply H1.
  intros; rewrite H9; induction  i as [| i Hreci].
  simpl in |- *; red in |- *; intro; elim Hyp_eq; apply Rle_antisym.
  apply (H15 0%nat); simpl in |- *; apply lt_O_Sn.
  rewrite <- Hyp_min; rewrite H6; simpl in H13; rewrite <- H13; right;
    reflexivity.
  elim H8; intros; rewrite <- H9; apply (H20 i); rewrite H9; rewrite H9 in H1;
    simpl in |- *; simpl in H1; apply lt_S_n; apply H1.
  rewrite H3 in H1; clear H4; unfold adapted_couple in H1; decompose [and] H1;
    clear H1; clear H H7 H9; cut (Rmax a b = b);
      [ intro; rewrite H in H5; rewrite <- H5; apply RList_P7;
        [ assumption | simpl in |- *; right; left; reflexivity ]
        | unfold Rmax in |- *; case (Rle_dec a b); intro;
          [ reflexivity | elim n; assumption ] ].
Qed.

Lemma StepFun_P11 :
  forall (a b r r1 r3 s1 s2 r4:R) (r2 lf1 s3 lf2:Rlist)
    (f:R -> R),
    a < b ->
    adapted_couple f a b (cons r (cons r1 r2)) (cons r3 lf1) ->
    adapted_couple_opt f a b (cons s1 (cons s2 s3)) (cons r4 lf2) -> r1 <= s2.
Proof.
  intros; unfold adapted_couple_opt in H1; elim H1; clear H1; intros;
    unfold adapted_couple in H0, H1; decompose [and] H0;
      decompose [and] H1; clear H0 H1; assert (H12 : r = s1).
  simpl in H10; simpl in H5; rewrite H10; rewrite H5; reflexivity.
  assert (H14 := H3 0%nat (lt_O_Sn _)); simpl in H14; elim H14; intro.
  assert (H15 := H7 0%nat (lt_O_Sn _)); simpl in H15; elim H15; intro.
  rewrite <- H12 in H1; case (Rle_dec r1 s2); intro; try assumption.
  assert (H16 : s2 < r1); auto with real.
  induction  s3 as [| r0 s3 Hrecs3].
  simpl in H9; rewrite H9 in H16; cut (r1 <= Rmax a b).
  intro; elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H17 H16)).
  rewrite <- H4; apply RList_P7;
    [ assumption | simpl in |- *; right; left; reflexivity ].
  clear Hrecs3; induction  lf2 as [| r5 lf2 Hreclf2].
  simpl in H11; discriminate.
  clear Hreclf2; assert (H17 : r3 = r4).
  set (x := (r + s2) / 2); assert (H17 := H8 0%nat (lt_O_Sn _));
    assert (H18 := H13 0%nat (lt_O_Sn _));
      unfold constant_D_eq, open_interval in H17, H18; simpl in H17;
        simpl in H18; rewrite <- (H17 x).
  rewrite <- (H18 x).
  reflexivity.
  rewrite <- H12; unfold x in |- *; split.
  apply Rmult_lt_reg_l with 2;
    [ prove_sup0
      | unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
        rewrite <- Rinv_r_sym;
          [ rewrite Rmult_1_l; rewrite double; apply Rplus_lt_compat_l; assumption
            | discrR ] ].
  apply Rmult_lt_reg_l with 2;
    [ prove_sup0
      | unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
        rewrite <- Rinv_r_sym;
          [ rewrite Rmult_1_l; rewrite (Rplus_comm r); rewrite double;
            apply Rplus_lt_compat_l; assumption
            | discrR ] ].
  unfold x in |- *; split.
  apply Rmult_lt_reg_l with 2;
    [ prove_sup0
      | unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
        rewrite <- Rinv_r_sym;
          [ rewrite Rmult_1_l; rewrite double; apply Rplus_lt_compat_l; assumption
            | discrR ] ].
  apply Rlt_trans with s2;
    [ apply Rmult_lt_reg_l with 2;
      [ prove_sup0
        | unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2));
          rewrite <- Rmult_assoc; rewrite <- Rinv_r_sym;
            [ rewrite Rmult_1_l; rewrite (Rplus_comm r); rewrite double;
              apply Rplus_lt_compat_l; assumption
              | discrR ] ]
      | assumption ].
  assert (H18 : f s2 = r3).
  apply (H8 0%nat);
    [ simpl in |- *; apply lt_O_Sn
      | unfold open_interval in |- *; simpl in |- *; split; assumption ].
  assert (H19 : r3 = r5).
  assert (H19 := H7 1%nat); simpl in H19;
    assert (H20 := H19 (lt_n_S _ _ (lt_O_Sn _))); elim H20;
      intro.
  set (x := (s2 + Rmin r1 r0) / 2); assert (H22 := H8 0%nat);
    assert (H23 := H13 1%nat); simpl in H22; simpl in H23;
      rewrite <- (H22 (lt_O_Sn _) x).
  rewrite <- (H23 (lt_n_S _ _ (lt_O_Sn _)) x).
  reflexivity.
  unfold open_interval in |- *; simpl in |- *; unfold x in |- *; split.
  apply Rmult_lt_reg_l with 2;
    [ prove_sup0
      | unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
        rewrite <- Rinv_r_sym;
          [ rewrite Rmult_1_l; rewrite double; apply Rplus_lt_compat_l;
            unfold Rmin in |- *; case (Rle_dec r1 r0); intro;
              assumption
            | discrR ] ].
  apply Rmult_lt_reg_l with 2;
    [ prove_sup0
      | unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
        rewrite <- Rinv_r_sym;
          [ rewrite Rmult_1_l; rewrite double;
            apply Rlt_le_trans with (r0 + Rmin r1 r0);
              [ do 2 rewrite <- (Rplus_comm (Rmin r1 r0)); apply Rplus_lt_compat_l;
                assumption
                | apply Rplus_le_compat_l; apply Rmin_r ]
            | discrR ] ].
  unfold open_interval in |- *; simpl in |- *; unfold x in |- *; split.
  apply Rlt_trans with s2;
    [ assumption
      | apply Rmult_lt_reg_l with 2;
        [ prove_sup0
          | unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2));
            rewrite <- Rmult_assoc; rewrite <- Rinv_r_sym;
              [ rewrite Rmult_1_l; rewrite double; apply Rplus_lt_compat_l;
                unfold Rmin in |- *; case (Rle_dec r1 r0);
                  intro; assumption
                | discrR ] ] ].
  apply Rmult_lt_reg_l with 2;
    [ prove_sup0
      | unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
        rewrite <- Rinv_r_sym;
          [ rewrite Rmult_1_l; rewrite double;
            apply Rlt_le_trans with (r1 + Rmin r1 r0);
              [ do 2 rewrite <- (Rplus_comm (Rmin r1 r0)); apply Rplus_lt_compat_l;
                assumption
                | apply Rplus_le_compat_l; apply Rmin_l ]
            | discrR ] ].
  elim H2; clear H2; intros; assert (H23 := H22 1%nat); simpl in H23;
    assert (H24 := H23 (lt_n_S _ _ (lt_O_Sn _))); elim H24;
      assumption.
  elim H2; intros; assert (H22 := H20 0%nat); simpl in H22;
    assert (H23 := H22 (lt_O_Sn _)); elim H23; intro;
      [ elim H24; rewrite <- H17; rewrite <- H19; reflexivity
        | elim H24; rewrite <- H17; assumption ].
  elim H2; clear H2; intros; assert (H17 := H16 0%nat); simpl in H17;
    elim (H17 (lt_O_Sn _)); assumption.
  rewrite <- H0; rewrite H12; apply (H7 0%nat); simpl in |- *; apply lt_O_Sn.
Qed.

Lemma StepFun_P12 :
  forall (a b:R) (f:R -> R) (l lf:Rlist),
    adapted_couple_opt f a b l lf -> adapted_couple_opt f b a l lf.
Proof.
  unfold adapted_couple_opt in |- *; unfold adapted_couple in |- *; intros;
    decompose [and] H; clear H; repeat split; try assumption.
  rewrite H0; unfold Rmin in |- *; case (Rle_dec a b); intro;
    case (Rle_dec b a); intro; try reflexivity.
  apply Rle_antisym; assumption.
  apply Rle_antisym; auto with real.
  rewrite H3; unfold Rmax in |- *; case (Rle_dec a b); intro;
    case (Rle_dec b a); intro; try reflexivity.
  apply Rle_antisym; assumption.
  apply Rle_antisym; auto with real.
Qed.

Lemma StepFun_P13 :
  forall (a b r r1 r3 s1 s2 r4:R) (r2 lf1 s3 lf2:Rlist)
    (f:R -> R),
    a <> b ->
    adapted_couple f a b (cons r (cons r1 r2)) (cons r3 lf1) ->
    adapted_couple_opt f a b (cons s1 (cons s2 s3)) (cons r4 lf2) -> r1 <= s2.
Proof.
  intros; case (total_order_T a b); intro.
  elim s; intro.
  eapply StepFun_P11; [ apply a0 | apply H0 | apply H1 ].
  elim H; assumption.
  eapply StepFun_P11;
    [ apply r0 | apply StepFun_P2; apply H0 | apply StepFun_P12; apply H1 ].
Qed.

Lemma StepFun_P14 :
  forall (f:R -> R) (l1 l2 lf1 lf2:Rlist) (a b:R),
    a <= b ->
    adapted_couple f a b l1 lf1 ->
    adapted_couple_opt f a b l2 lf2 -> Int_SF lf1 l1 = Int_SF lf2 l2.
Proof.
  simple induction l1.
  intros l2 lf1 lf2 a b Hyp H H0; unfold adapted_couple in H; decompose [and] H;
    clear H H0 H2 H3 H1 H6; simpl in H4; discriminate.
  simple induction r0.
  intros; case (Req_dec a b); intro.
  unfold adapted_couple_opt in H2; elim H2; intros; rewrite (StepFun_P8 H4 H3);
    rewrite (StepFun_P8 H1 H3); reflexivity.
  assert (H4 := StepFun_P9 H1 H3); simpl in H4;
    elim (le_Sn_O _ (le_S_n _ _ H4)).
  intros; clear H; unfold adapted_couple_opt in H3; elim H3; clear H3; intros;
    case (Req_dec a b); intro.
  rewrite (StepFun_P8 H2 H4); rewrite (StepFun_P8 H H4); reflexivity.
  assert (Hyp_min : Rmin a b = a).
  unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; assumption ].
  assert (Hyp_max : Rmax a b = b).
  unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; assumption ].
  elim (RList_P20 _ (StepFun_P9 H H4)); intros s1 [s2 [s3 H5]]; rewrite H5 in H;
    rewrite H5; induction  lf1 as [| r3 lf1 Hreclf1].
  unfold adapted_couple in H2; decompose [and] H2;
    clear H H2 H4 H5 H3 H6 H8 H7 H11; simpl in H9; discriminate.
  clear Hreclf1; induction  lf2 as [| r4 lf2 Hreclf2].
  unfold adapted_couple in H; decompose [and] H;
    clear H H2 H4 H5 H3 H6 H8 H7 H11; simpl in H9; discriminate.
  clear Hreclf2; assert (H6 : r = s1).
  unfold adapted_couple in H, H2; decompose [and] H; decompose [and] H2;
    clear H H2; simpl in H13; simpl in H8; rewrite H13;
      rewrite H8; reflexivity.
  assert (H7 : r3 = r4 \/ r = r1).
  case (Req_dec r r1); intro.
  right; assumption.
  left; cut (r1 <= s2).
  intro; unfold adapted_couple in H2, H; decompose [and] H; decompose [and] H2;
    clear H H2; set (x := (r + r1) / 2); assert (H18 := H14 0%nat);
      assert (H20 := H19 0%nat); unfold constant_D_eq, open_interval in H18, H20;
        simpl in H18; simpl in H20; rewrite <- (H18 (lt_O_Sn _) x).
  rewrite <- (H20 (lt_O_Sn _) x).
  reflexivity.
  assert (H21 := H13 0%nat (lt_O_Sn _)); simpl in H21; elim H21; intro;
    [ idtac | elim H7; assumption ]; unfold x in |- *;
      split.
  apply Rmult_lt_reg_l with 2;
    [ prove_sup0
      | unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
        rewrite <- Rinv_r_sym;
          [ rewrite Rmult_1_l; rewrite double; apply Rplus_lt_compat_l; apply H
            | discrR ] ].
  apply Rmult_lt_reg_l with 2;
    [ prove_sup0
      | unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
        rewrite <- Rinv_r_sym;
          [ rewrite Rmult_1_l; rewrite <- (Rplus_comm r1); rewrite double;
            apply Rplus_lt_compat_l; apply H
            | discrR ] ].
  rewrite <- H6; assert (H21 := H13 0%nat (lt_O_Sn _)); simpl in H21; elim H21;
    intro; [ idtac | elim H7; assumption ]; unfold x in |- *;
      split.
  apply Rmult_lt_reg_l with 2;
    [ prove_sup0
      | unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
        rewrite <- Rinv_r_sym;
          [ rewrite Rmult_1_l; rewrite double; apply Rplus_lt_compat_l; apply H
            | discrR ] ].
  apply Rlt_le_trans with r1;
    [ apply Rmult_lt_reg_l with 2;
      [ prove_sup0
        | unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2));
          rewrite <- Rmult_assoc; rewrite <- Rinv_r_sym;
            [ rewrite Rmult_1_l; rewrite <- (Rplus_comm r1); rewrite double;
              apply Rplus_lt_compat_l; apply H
              | discrR ] ]
      | assumption ].
  eapply StepFun_P13.
  apply H4.
  apply H2.
  unfold adapted_couple_opt in |- *; split.
  apply H.
  rewrite H5 in H3; apply H3.
  assert (H8 : r1 <= s2).
  eapply StepFun_P13.
  apply H4.
  apply H2.
  unfold adapted_couple_opt in |- *; split.
  apply H.
  rewrite H5 in H3; apply H3.
  elim H7; intro.
  simpl in |- *; elim H8; intro.
  replace (r4 * (s2 - s1)) with (r3 * (r1 - r) + r3 * (s2 - r1));
  [ idtac | rewrite H9; rewrite H6; ring ].
  rewrite Rplus_assoc; apply Rplus_eq_compat_l;
    change
      (Int_SF lf1 (cons r1 r2) = Int_SF (cons r3 lf2) (cons r1 (cons s2 s3)))
      in |- *; apply H0 with r1 b.
  unfold adapted_couple in H2; decompose [and] H2; clear H2;
    replace b with (Rmax a b).
  rewrite <- H12; apply RList_P7;
    [ assumption | simpl in |- *; right; left; reflexivity ].
  eapply StepFun_P7.
  apply H1.
  apply H2.
  unfold adapted_couple_opt in |- *; split.
  apply StepFun_P7 with a a r3.
  apply H1.
  unfold adapted_couple in H2, H; decompose [and] H2; decompose [and] H;
    clear H H2; assert (H20 : r = a).
  simpl in H13; rewrite H13; apply Hyp_min.
  unfold adapted_couple in |- *; repeat split.
  unfold ordered_Rlist in |- *; intros; simpl in H; induction  i as [| i Hreci].
  simpl in |- *; rewrite <- H20; apply (H11 0%nat).
  simpl in |- *; apply lt_O_Sn.
  induction  i as [| i Hreci0].
  simpl in |- *; assumption.
  change (pos_Rl (cons s2 s3) i <= pos_Rl (cons s2 s3) (S i)) in |- *;
    apply (H15 (S i)); simpl in |- *; apply lt_S_n; assumption.
  simpl in |- *; symmetry  in |- *; apply Hyp_min.
  rewrite <- H17; reflexivity.
  simpl in H19; simpl in |- *; rewrite H19; reflexivity.
  intros; simpl in H; unfold constant_D_eq, open_interval in |- *; intros;
    induction  i as [| i Hreci].
  simpl in |- *; apply (H16 0%nat).
  simpl in |- *; apply lt_O_Sn.
  simpl in H2; rewrite <- H20 in H2; unfold open_interval in |- *;
    simpl in |- *; apply H2.
  clear Hreci; induction  i as [| i Hreci].
  simpl in |- *; simpl in H2; rewrite H9; apply (H21 0%nat).
  simpl in |- *; apply lt_O_Sn.
  unfold open_interval in |- *; simpl in |- *; elim H2; intros; split.
  apply Rle_lt_trans with r1; try assumption; rewrite <- H6; apply (H11 0%nat);
    simpl in |- *; apply lt_O_Sn.
  assumption.
  clear Hreci; simpl in |- *; apply (H21 (S i)).
  simpl in |- *; apply lt_S_n; assumption.
  unfold open_interval in |- *; apply H2.
  elim H3; clear H3; intros; split.
  rewrite H9;
    change
      (forall i:nat,
        (i < pred (Rlength (cons r4 lf2)))%nat ->
        pos_Rl (cons r4 lf2) i <> pos_Rl (cons r4 lf2) (S i) \/
        f (pos_Rl (cons s1 (cons s2 s3)) (S i)) <> pos_Rl (cons r4 lf2) i)
      in |- *; rewrite <- H5; apply H3.
  rewrite H5 in H11; intros; simpl in H12; induction  i as [| i Hreci].
  simpl in |- *; red in |- *; intro; rewrite H13 in H10;
    elim (Rlt_irrefl _ H10).
  clear Hreci; apply (H11 (S i)); simpl in |- *; apply H12.
  rewrite H9; rewrite H10; rewrite H6; apply Rplus_eq_compat_l; rewrite <- H10;
    apply H0 with r1 b.
  unfold adapted_couple in H2; decompose [and] H2; clear H2;
    replace b with (Rmax a b).
  rewrite <- H12; apply RList_P7;
    [ assumption | simpl in |- *; right; left; reflexivity ].
  eapply StepFun_P7.
  apply H1.
  apply H2.
  unfold adapted_couple_opt in |- *; split.
  apply StepFun_P7 with a a r3.
  apply H1.
  unfold adapted_couple in H2, H; decompose [and] H2; decompose [and] H;
    clear H H2; assert (H20 : r = a).
  simpl in H13; rewrite H13; apply Hyp_min.
  unfold adapted_couple in |- *; repeat split.
  unfold ordered_Rlist in |- *; intros; simpl in H; induction  i as [| i Hreci].
  simpl in |- *; rewrite <- H20; apply (H11 0%nat); simpl in |- *;
    apply lt_O_Sn.
  rewrite H10; apply (H15 (S i)); simpl in |- *; assumption.
  simpl in |- *; symmetry  in |- *; apply Hyp_min.
  rewrite <- H17; rewrite H10; reflexivity.
  simpl in H19; simpl in |- *; apply H19.
  intros; simpl in H; unfold constant_D_eq, open_interval in |- *; intros;
    induction  i as [| i Hreci].
  simpl in |- *; apply (H16 0%nat).
  simpl in |- *; apply lt_O_Sn.
  simpl in H2; rewrite <- H20 in H2; unfold open_interval in |- *;
    simpl in |- *; apply H2.
  clear Hreci; simpl in |- *; apply (H21 (S i)).
  simpl in |- *; assumption.
  rewrite <- H10; unfold open_interval in |- *; apply H2.
  elim H3; clear H3; intros; split.
  rewrite H5 in H3; intros; apply (H3 (S i)).
  simpl in |- *; replace (Rlength lf2) with (S (pred (Rlength lf2))).
  apply lt_n_S; apply H12.
  symmetry  in |- *; apply S_pred with 0%nat; apply neq_O_lt; red in |- *;
    intro; rewrite <- H13 in H12; elim (lt_n_O _ H12).
  intros; simpl in H12; rewrite H10; rewrite H5 in H11; apply (H11 (S i));
    simpl in |- *; apply lt_n_S; apply H12.
  simpl in |- *; rewrite H9; unfold Rminus in |- *; rewrite Rplus_opp_r;
    rewrite Rmult_0_r; rewrite Rplus_0_l;
      change
        (Int_SF lf1 (cons r1 r2) = Int_SF (cons r4 lf2) (cons s1 (cons s2 s3)))
        in |- *; eapply H0.
  apply H1.
  2: rewrite H5 in H3; unfold adapted_couple_opt in |- *; split; assumption.
  assert (H10 : r = a).
  unfold adapted_couple in H2; decompose [and] H2; clear H2; simpl in H12;
    rewrite H12; apply Hyp_min.
  rewrite <- H9; rewrite H10; apply StepFun_P7 with a r r3;
    [ apply H1
      | pattern a at 2 in |- *; rewrite <- H10; pattern r at 2 in |- *; rewrite H9;
        apply H2 ].
Qed.

Lemma StepFun_P15 :
  forall (f:R -> R) (l1 l2 lf1 lf2:Rlist) (a b:R),
    adapted_couple f a b l1 lf1 ->
    adapted_couple_opt f a b l2 lf2 -> Int_SF lf1 l1 = Int_SF lf2 l2.
Proof.
  intros; case (Rle_dec a b); intro;
    [ apply (StepFun_P14 r H H0)
      | assert (H1 : b <= a);
        [ auto with real
          | eapply StepFun_P14;
            [ apply H1 | apply StepFun_P2; apply H | apply StepFun_P12; apply H0 ] ] ].
Qed.

Lemma StepFun_P16 :
  forall (f:R -> R) (l lf:Rlist) (a b:R),
    adapted_couple f a b l lf ->
    exists l' : Rlist,
      (exists lf' : Rlist, adapted_couple_opt f a b l' lf').
Proof.
  intros; case (Rle_dec a b); intro;
    [ apply (StepFun_P10 r H)
      | assert (H1 : b <= a);
        [ auto with real
          | assert (H2 := StepFun_P10 H1 (StepFun_P2 H)); elim H2;
            intros l' [lf' H3]; exists l'; exists lf'; apply StepFun_P12;
              assumption ] ].
Qed.

Lemma StepFun_P17 :
  forall (f:R -> R) (l1 l2 lf1 lf2:Rlist) (a b:R),
    adapted_couple f a b l1 lf1 ->
    adapted_couple f a b l2 lf2 -> Int_SF lf1 l1 = Int_SF lf2 l2.
Proof.
  intros; elim (StepFun_P16 H); intros l' [lf' H1]; rewrite (StepFun_P15 H H1);
    rewrite (StepFun_P15 H0 H1); reflexivity.
Qed.

Lemma StepFun_P18 :
  forall a b c:R, RiemannInt_SF (mkStepFun (StepFun_P4 a b c)) = c * (b - a).
Proof.
  intros; unfold RiemannInt_SF in |- *; case (Rle_dec a b); intro.
  replace
  (Int_SF (subdivision_val (mkStepFun (StepFun_P4 a b c)))
    (subdivision (mkStepFun (StepFun_P4 a b c)))) with
  (Int_SF (cons c nil) (cons a (cons b nil)));
  [ simpl in |- *; ring
    | apply StepFun_P17 with (fct_cte c) a b;
      [ apply StepFun_P3; assumption
        | apply (StepFun_P1 (mkStepFun (StepFun_P4 a b c))) ] ].
  replace
  (Int_SF (subdivision_val (mkStepFun (StepFun_P4 a b c)))
    (subdivision (mkStepFun (StepFun_P4 a b c)))) with
  (Int_SF (cons c nil) (cons b (cons a nil)));
  [ simpl in |- *; ring
    | apply StepFun_P17 with (fct_cte c) a b;
      [ apply StepFun_P2; apply StepFun_P3; auto with real
        | apply (StepFun_P1 (mkStepFun (StepFun_P4 a b c))) ] ].
Qed.

Lemma StepFun_P19 :
  forall (l1:Rlist) (f g:R -> R) (l:R),
    Int_SF (FF l1 (fun x:R => f x + l * g x)) l1 =
    Int_SF (FF l1 f) l1 + l * Int_SF (FF l1 g) l1.
Proof.
  intros; induction  l1 as [| r l1 Hrecl1];
    [ simpl in |- *; ring
      | induction  l1 as [| r0 l1 Hrecl0]; simpl in |- *;
        [ ring | simpl in Hrecl1; rewrite Hrecl1; ring ] ].
Qed.

Lemma StepFun_P20 :
  forall (l:Rlist) (f:R -> R),
    (0 < Rlength l)%nat -> Rlength l = S (Rlength (FF l f)).
Proof.
  intros l f H; induction l;
    [ elim (lt_irrefl _ H)
      | simpl in |- *; rewrite RList_P18; rewrite RList_P14; reflexivity ].
Qed.

Lemma StepFun_P21 :
  forall (a b:R) (f:R -> R) (l:Rlist),
    is_subdivision f a b l -> adapted_couple f a b l (FF l f).
Proof.
  intros; unfold adapted_couple in |- *; unfold is_subdivision in X;
    unfold adapted_couple in X; elim X; clear X; intros;
      decompose [and] p; clear p; repeat split; try assumption.
  apply StepFun_P20; rewrite H2; apply lt_O_Sn.
  intros; assert (H5 := H4 _ H3); unfold constant_D_eq, open_interval in H5;
    unfold constant_D_eq, open_interval in |- *; intros;
      induction  l as [| r l Hrecl].
  discriminate.
  unfold FF in |- *; rewrite RList_P12.
  simpl in |- *;
    change (f x0 = f (pos_Rl (mid_Rlist (cons r l) r) (S i))) in |- *;
      rewrite RList_P13; try assumption; rewrite (H5 x0 H6);
        rewrite H5.
  reflexivity.
  split.
  apply Rmult_lt_reg_l with 2;
    [ prove_sup0
      | unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
        rewrite <- Rinv_r_sym;
          [ rewrite Rmult_1_l; rewrite double; apply Rplus_lt_compat_l; elim H6;
            intros; apply Rlt_trans with x0; assumption
            | discrR ] ].
  apply Rmult_lt_reg_l with 2;
    [ prove_sup0
      | unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
        rewrite <- Rinv_r_sym;
          [ rewrite Rmult_1_l; rewrite double;
            rewrite (Rplus_comm (pos_Rl (cons r l) i));
              apply Rplus_lt_compat_l; elim H6; intros; apply Rlt_trans with x0;
                assumption
            | discrR ] ].
  rewrite RList_P14; simpl in H3; apply H3.
Qed.

Lemma StepFun_P22 :
  forall (a b:R) (f g:R -> R) (lf lg:Rlist),
    a <= b ->
    is_subdivision f a b lf ->
    is_subdivision g a b lg -> is_subdivision f a b (cons_ORlist lf lg).
Proof.
  unfold is_subdivision in |- *; intros a b f g lf lg Hyp X X0; elim X; elim X0;
    clear X X0; intros lg0 p lf0 p0; assert (Hyp_min : Rmin a b = a).
  unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; assumption ].
  assert (Hyp_max : Rmax a b = b).
  unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; assumption ].
  apply existT with (FF (cons_ORlist lf lg) f); unfold adapted_couple in p, p0;
    decompose [and] p; decompose [and] p0; clear p p0;
      rewrite Hyp_min in H6; rewrite Hyp_min in H1; rewrite Hyp_max in H0;
        rewrite Hyp_max in H5; unfold adapted_couple in |- *;
          repeat split.
  apply RList_P2; assumption.
  rewrite Hyp_min; symmetry  in |- *; apply Rle_antisym.
  induction  lf as [| r lf Hreclf].
  simpl in |- *; right; symmetry  in |- *; assumption.
  assert
    (H10 :
      In (pos_Rl (cons_ORlist (cons r lf) lg) 0) (cons_ORlist (cons r lf) lg)).
  elim
    (RList_P3 (cons_ORlist (cons r lf) lg)
      (pos_Rl (cons_ORlist (cons r lf) lg) 0)); intros _ H10;
    apply H10; exists 0%nat; split;
      [ reflexivity | rewrite RList_P11; simpl in |- *; apply lt_O_Sn ].
  elim (RList_P9 (cons r lf) lg (pos_Rl (cons_ORlist (cons r lf) lg) 0));
    intros H12 _; assert (H13 := H12 H10); elim H13; intro.
  elim (RList_P3 (cons r lf) (pos_Rl (cons_ORlist (cons r lf) lg) 0));
    intros H11 _; assert (H14 := H11 H8); elim H14; intros;
      elim H15; clear H15; intros; rewrite H15; rewrite <- H6;
        elim (RList_P6 (cons r lf)); intros; apply H17;
          [ assumption | apply le_O_n | assumption ].
  elim (RList_P3 lg (pos_Rl (cons_ORlist (cons r lf) lg) 0)); intros H11 _;
    assert (H14 := H11 H8); elim H14; intros; elim H15;
      clear H15; intros; rewrite H15; rewrite <- H1; elim (RList_P6 lg);
        intros; apply H17; [ assumption | apply le_O_n | assumption ].
  induction  lf as [| r lf Hreclf].
  simpl in |- *; right; assumption.
  assert (H8 : In a (cons_ORlist (cons r lf) lg)).
  elim (RList_P9 (cons r lf) lg a); intros; apply H10; left;
    elim (RList_P3 (cons r lf) a); intros; apply H12;
      exists 0%nat; split;
        [ symmetry  in |- *; assumption | simpl in |- *; apply lt_O_Sn ].
  apply RList_P5; [ apply RList_P2; assumption | assumption ].
  rewrite Hyp_max; apply Rle_antisym.
  induction  lf as [| r lf Hreclf].
  simpl in |- *; right; assumption.
  assert
    (H8 :
      In
      (pos_Rl (cons_ORlist (cons r lf) lg)
        (pred (Rlength (cons_ORlist (cons r lf) lg))))
      (cons_ORlist (cons r lf) lg)).
  elim
    (RList_P3 (cons_ORlist (cons r lf) lg)
      (pos_Rl (cons_ORlist (cons r lf) lg)
        (pred (Rlength (cons_ORlist (cons r lf) lg)))));
    intros _ H10; apply H10;
      exists (pred (Rlength (cons_ORlist (cons r lf) lg)));
        split; [ reflexivity | rewrite RList_P11; simpl in |- *; apply lt_n_Sn ].
  elim
    (RList_P9 (cons r lf) lg
      (pos_Rl (cons_ORlist (cons r lf) lg)
        (pred (Rlength (cons_ORlist (cons r lf) lg)))));
    intros H10 _.
  assert (H11 := H10 H8); elim H11; intro.
  elim
    (RList_P3 (cons r lf)
      (pos_Rl (cons_ORlist (cons r lf) lg)
        (pred (Rlength (cons_ORlist (cons r lf) lg)))));
    intros H13 _; assert (H14 := H13 H12); elim H14; intros;
      elim H15; clear H15; intros; rewrite H15; rewrite <- H5;
        elim (RList_P6 (cons r lf)); intros; apply H17;
          [ assumption
            | simpl in |- *; simpl in H14; apply lt_n_Sm_le; assumption
            | simpl in |- *; apply lt_n_Sn ].
  elim
    (RList_P3 lg
      (pos_Rl (cons_ORlist (cons r lf) lg)
        (pred (Rlength (cons_ORlist (cons r lf) lg)))));
    intros H13 _; assert (H14 := H13 H12); elim H14; intros;
      elim H15; clear H15; intros.
  rewrite H15; assert (H17 : Rlength lg = S (pred (Rlength lg))).
  apply S_pred with 0%nat; apply neq_O_lt; red in |- *; intro;
    rewrite <- H17 in H16; elim (lt_n_O _ H16).
  rewrite <- H0; elim (RList_P6 lg); intros; apply H18;
    [ assumption
      | rewrite H17 in H16; apply lt_n_Sm_le; assumption
      | apply lt_pred_n_n; rewrite H17; apply lt_O_Sn ].
  induction  lf as [| r lf Hreclf].
  simpl in |- *; right; symmetry  in |- *; assumption.
  assert (H8 : In b (cons_ORlist (cons r lf) lg)).
  elim (RList_P9 (cons r lf) lg b); intros; apply H10; left;
    elim (RList_P3 (cons r lf) b); intros; apply H12;
      exists (pred (Rlength (cons r lf))); split;
        [ symmetry  in |- *; assumption | simpl in |- *; apply lt_n_Sn ].
  apply RList_P7; [ apply RList_P2; assumption | assumption ].
  apply StepFun_P20; rewrite RList_P11; rewrite H2; rewrite H7; simpl in |- *;
    apply lt_O_Sn.
  intros; unfold constant_D_eq, open_interval in |- *; intros;
    cut
      (exists l : R,
        constant_D_eq f
        (open_interval (pos_Rl (cons_ORlist lf lg) i)
          (pos_Rl (cons_ORlist lf lg) (S i))) l).
  intros; elim H11; clear H11; intros; assert (H12 := H11);
    assert
      (Hyp_cons :
        exists r : R, (exists r0 : Rlist, cons_ORlist lf lg = cons r r0)).
  apply RList_P19; red in |- *; intro; rewrite H13 in H8; elim (lt_n_O _ H8).
  elim Hyp_cons; clear Hyp_cons; intros r [r0 Hyp_cons]; rewrite Hyp_cons;
    unfold FF in |- *; rewrite RList_P12.
  change (f x = f (pos_Rl (mid_Rlist (cons r r0) r) (S i))) in |- *;
    rewrite <- Hyp_cons; rewrite RList_P13.
  assert (H13 := RList_P2 _ _ H _ H8); elim H13; intro.
  unfold constant_D_eq, open_interval in H11, H12; rewrite (H11 x H10);
    assert
      (H15 :
        pos_Rl (cons_ORlist lf lg) i <
        (pos_Rl (cons_ORlist lf lg) i + pos_Rl (cons_ORlist lf lg) (S i)) / 2 <
        pos_Rl (cons_ORlist lf lg) (S i)).
  split.
  apply Rmult_lt_reg_l with 2;
    [ prove_sup0
      | unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
        rewrite <- Rinv_r_sym;
          [ rewrite Rmult_1_l; rewrite double; apply Rplus_lt_compat_l; assumption
            | discrR ] ].
  apply Rmult_lt_reg_l with 2;
    [ prove_sup0
      | unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
        rewrite <- Rinv_r_sym;
          [ rewrite Rmult_1_l; rewrite double;
            rewrite (Rplus_comm (pos_Rl (cons_ORlist lf lg) i));
              apply Rplus_lt_compat_l; assumption
            | discrR ] ].
  rewrite (H11 _ H15); reflexivity.
  elim H10; intros; rewrite H14 in H15;
    elim (Rlt_irrefl _ (Rlt_trans _ _ _ H16 H15)).
  apply H8.
  rewrite RList_P14; rewrite Hyp_cons in H8; simpl in H8; apply H8.
  assert (H11 : a < b).
  apply Rle_lt_trans with (pos_Rl (cons_ORlist lf lg) i).
  rewrite <- H6; rewrite <- (RList_P15 lf lg).
  elim (RList_P6 (cons_ORlist lf lg)); intros; apply H11.
  apply RList_P2; assumption.
  apply le_O_n.
  apply lt_trans with (pred (Rlength (cons_ORlist lf lg)));
    [ assumption
      | apply lt_pred_n_n; apply neq_O_lt; red in |- *; intro;
        rewrite <- H13 in H8; elim (lt_n_O _ H8) ].
  assumption.
  assumption.
  rewrite H1; assumption.
  apply Rlt_le_trans with (pos_Rl (cons_ORlist lf lg) (S i)).
  elim H10; intros; apply Rlt_trans with x; assumption.
  rewrite <- H5; rewrite <- (RList_P16 lf lg); try assumption.
  elim (RList_P6 (cons_ORlist lf lg)); intros; apply H11.
  apply RList_P2; assumption.
  apply lt_n_Sm_le; apply lt_n_S; assumption.
  apply lt_pred_n_n; apply neq_O_lt; red in |- *; intro; rewrite <- H13 in H8;
    elim (lt_n_O _ H8).
  rewrite H0; assumption.
  set
    (I :=
      fun j:nat =>
        pos_Rl lf j <= pos_Rl (cons_ORlist lf lg) i /\ (j < Rlength lf)%nat);
    assert (H12 : Nbound I).
  unfold Nbound in |- *; exists (Rlength lf); intros; unfold I in H12; elim H12;
    intros; apply lt_le_weak; assumption.
  assert (H13 :  exists n : nat, I n).
  exists 0%nat; unfold I in |- *; split.
  apply Rle_trans with (pos_Rl (cons_ORlist lf lg) 0).
  right; symmetry  in |- *.
  apply RList_P15; try assumption; rewrite H1; assumption.
  elim (RList_P6 (cons_ORlist lf lg)); intros; apply H13.
  apply RList_P2; assumption.
  apply le_O_n.
  apply lt_trans with (pred (Rlength (cons_ORlist lf lg))).
  assumption.
  apply lt_pred_n_n; apply neq_O_lt; red in |- *; intro; rewrite <- H15 in H8;
    elim (lt_n_O _ H8).
  apply neq_O_lt; red in |- *; intro; rewrite <- H13 in H5;
    rewrite <- H6 in H11; rewrite <- H5 in H11; elim (Rlt_irrefl _ H11).
  assert (H14 := Nzorn H13 H12); elim H14; clear H14; intros x0 H14;
    exists (pos_Rl lf0 x0); unfold constant_D_eq, open_interval in |- *;
      intros; assert (H16 := H9 x0); assert (H17 : (x0 < pred (Rlength lf))%nat).
  elim H14; clear H14; intros; unfold I in H14; elim H14; clear H14; intros;
    apply lt_S_n; replace (S (pred (Rlength lf))) with (Rlength lf).
  inversion H18.
  2: apply lt_n_S; assumption.
  cut (x0 = pred (Rlength lf)).
  intro; rewrite H19 in H14; rewrite H5 in H14;
    cut (pos_Rl (cons_ORlist lf lg) i < b).
  intro; elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H14 H21)).
  apply Rlt_le_trans with (pos_Rl (cons_ORlist lf lg) (S i)).
  elim H10; intros; apply Rlt_trans with x; assumption.
  rewrite <- H5;
    apply Rle_trans with
      (pos_Rl (cons_ORlist lf lg) (pred (Rlength (cons_ORlist lf lg)))).
  elim (RList_P6 (cons_ORlist lf lg)); intros; apply H21.
  apply RList_P2; assumption.
  apply lt_n_Sm_le; apply lt_n_S; assumption.
  apply lt_pred_n_n; apply neq_O_lt; red in |- *; intro; rewrite <- H23 in H8;
    elim (lt_n_O _ H8).
  right; apply RList_P16; try assumption; rewrite H0; assumption.
  rewrite <- H20; reflexivity.
  apply S_pred with 0%nat; apply neq_O_lt; red in |- *; intro;
    rewrite <- H19 in H18; elim (lt_n_O _ H18).
  assert (H18 := H16 H17); unfold constant_D_eq, open_interval in H18;
    rewrite (H18 x1).
  reflexivity.
  elim H15; clear H15; intros; elim H14; clear H14; intros; unfold I in H14;
    elim H14; clear H14; intros; split.
  apply Rle_lt_trans with (pos_Rl (cons_ORlist lf lg) i); assumption.
  apply Rlt_le_trans with (pos_Rl (cons_ORlist lf lg) (S i)); try assumption.
  assert (H22 : (S x0 < Rlength lf)%nat).
  replace (Rlength lf) with (S (pred (Rlength lf)));
  [ apply lt_n_S; assumption
    | symmetry  in |- *; apply S_pred with 0%nat; apply neq_O_lt; red in |- *;
      intro; rewrite <- H22 in H21; elim (lt_n_O _ H21) ].
  elim (Rle_dec (pos_Rl lf (S x0)) (pos_Rl (cons_ORlist lf lg) i)); intro.
  assert (H23 : (S x0 <= x0)%nat).
  apply H20; unfold I in |- *; split; assumption.
  elim (le_Sn_n _ H23).
  assert (H23 : pos_Rl (cons_ORlist lf lg) i < pos_Rl lf (S x0)).
  auto with real.
  clear b0; apply RList_P17; try assumption.
  apply RList_P2; assumption.
  elim (RList_P9 lf lg (pos_Rl lf (S x0))); intros; apply H25; left;
    elim (RList_P3 lf (pos_Rl lf (S x0))); intros; apply H27;
      exists (S x0); split; [ reflexivity | apply H22 ].
Qed.

Lemma StepFun_P23 :
  forall (a b:R) (f g:R -> R) (lf lg:Rlist),
    is_subdivision f a b lf ->
    is_subdivision g a b lg -> is_subdivision f a b (cons_ORlist lf lg).
Proof.
  intros; case (Rle_dec a b); intro;
    [ apply StepFun_P22 with g; assumption
      | apply StepFun_P5; apply StepFun_P22 with g;
        [ auto with real
          | apply StepFun_P5; assumption
          | apply StepFun_P5; assumption ] ].
Qed.

Lemma StepFun_P24 :
  forall (a b:R) (f g:R -> R) (lf lg:Rlist),
    a <= b ->
    is_subdivision f a b lf ->
    is_subdivision g a b lg -> is_subdivision g a b (cons_ORlist lf lg).
Proof.
  unfold is_subdivision in |- *; intros a b f g lf lg Hyp X X0; elim X; elim X0;
    clear X X0; intros lg0 p lf0 p0; assert (Hyp_min : Rmin a b = a).
  unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; assumption ].
  assert (Hyp_max : Rmax a b = b).
  unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; assumption ].
  apply existT with (FF (cons_ORlist lf lg) g); unfold adapted_couple in p, p0;
    decompose [and] p; decompose [and] p0; clear p p0;
      rewrite Hyp_min in H1; rewrite Hyp_min in H6; rewrite Hyp_max in H0;
        rewrite Hyp_max in H5; unfold adapted_couple in |- *;
          repeat split.
  apply RList_P2; assumption.
  rewrite Hyp_min; symmetry  in |- *; apply Rle_antisym.
  induction  lf as [| r lf Hreclf].
  simpl in |- *; right; symmetry  in |- *; assumption.
  assert
    (H10 :
      In (pos_Rl (cons_ORlist (cons r lf) lg) 0) (cons_ORlist (cons r lf) lg)).
  elim
    (RList_P3 (cons_ORlist (cons r lf) lg)
      (pos_Rl (cons_ORlist (cons r lf) lg) 0)); intros _ H10;
    apply H10; exists 0%nat; split;
      [ reflexivity | rewrite RList_P11; simpl in |- *; apply lt_O_Sn ].
  elim (RList_P9 (cons r lf) lg (pos_Rl (cons_ORlist (cons r lf) lg) 0));
    intros H12 _; assert (H13 := H12 H10); elim H13; intro.
  elim (RList_P3 (cons r lf) (pos_Rl (cons_ORlist (cons r lf) lg) 0));
    intros H11 _; assert (H14 := H11 H8); elim H14; intros;
      elim H15; clear H15; intros; rewrite H15; rewrite <- H6;
        elim (RList_P6 (cons r lf)); intros; apply H17;
          [ assumption | apply le_O_n | assumption ].
  elim (RList_P3 lg (pos_Rl (cons_ORlist (cons r lf) lg) 0)); intros H11 _;
    assert (H14 := H11 H8); elim H14; intros; elim H15;
      clear H15; intros; rewrite H15; rewrite <- H1; elim (RList_P6 lg);
        intros; apply H17; [ assumption | apply le_O_n | assumption ].
  induction  lf as [| r lf Hreclf].
  simpl in |- *; right; assumption.
  assert (H8 : In a (cons_ORlist (cons r lf) lg)).
  elim (RList_P9 (cons r lf) lg a); intros; apply H10; left;
    elim (RList_P3 (cons r lf) a); intros; apply H12;
      exists 0%nat; split;
        [ symmetry  in |- *; assumption | simpl in |- *; apply lt_O_Sn ].
  apply RList_P5; [ apply RList_P2; assumption | assumption ].
  rewrite Hyp_max; apply Rle_antisym.
  induction  lf as [| r lf Hreclf].
  simpl in |- *; right; assumption.
  assert
    (H8 :
      In
      (pos_Rl (cons_ORlist (cons r lf) lg)
        (pred (Rlength (cons_ORlist (cons r lf) lg))))
      (cons_ORlist (cons r lf) lg)).
  elim
    (RList_P3 (cons_ORlist (cons r lf) lg)
      (pos_Rl (cons_ORlist (cons r lf) lg)
        (pred (Rlength (cons_ORlist (cons r lf) lg)))));
    intros _ H10; apply H10;
      exists (pred (Rlength (cons_ORlist (cons r lf) lg)));
        split; [ reflexivity | rewrite RList_P11; simpl in |- *; apply lt_n_Sn ].
  elim
    (RList_P9 (cons r lf) lg
      (pos_Rl (cons_ORlist (cons r lf) lg)
        (pred (Rlength (cons_ORlist (cons r lf) lg)))));
    intros H10 _; assert (H11 := H10 H8); elim H11; intro.
  elim
    (RList_P3 (cons r lf)
      (pos_Rl (cons_ORlist (cons r lf) lg)
        (pred (Rlength (cons_ORlist (cons r lf) lg)))));
    intros H13 _; assert (H14 := H13 H12); elim H14; intros;
      elim H15; clear H15; intros; rewrite H15; rewrite <- H5;
        elim (RList_P6 (cons r lf)); intros; apply H17;
          [ assumption
            | simpl in |- *; simpl in H14; apply lt_n_Sm_le; assumption
            | simpl in |- *; apply lt_n_Sn ].
  elim
    (RList_P3 lg
      (pos_Rl (cons_ORlist (cons r lf) lg)
        (pred (Rlength (cons_ORlist (cons r lf) lg)))));
    intros H13 _; assert (H14 := H13 H12); elim H14; intros;
      elim H15; clear H15; intros; rewrite H15;
        assert (H17 : Rlength lg = S (pred (Rlength lg))).
  apply S_pred with 0%nat; apply neq_O_lt; red in |- *; intro;
    rewrite <- H17 in H16; elim (lt_n_O _ H16).
  rewrite <- H0; elim (RList_P6 lg); intros; apply H18;
    [ assumption
      | rewrite H17 in H16; apply lt_n_Sm_le; assumption
      | apply lt_pred_n_n; rewrite H17; apply lt_O_Sn ].
  induction  lf as [| r lf Hreclf].
  simpl in |- *; right; symmetry  in |- *; assumption.
  assert (H8 : In b (cons_ORlist (cons r lf) lg)).
  elim (RList_P9 (cons r lf) lg b); intros; apply H10; left;
    elim (RList_P3 (cons r lf) b); intros; apply H12;
      exists (pred (Rlength (cons r lf))); split;
        [ symmetry  in |- *; assumption | simpl in |- *; apply lt_n_Sn ].
  apply RList_P7; [ apply RList_P2; assumption | assumption ].
  apply StepFun_P20; rewrite RList_P11; rewrite H7; rewrite H2; simpl in |- *;
    apply lt_O_Sn.
  unfold constant_D_eq, open_interval in |- *; intros;
    cut
      (exists l : R,
        constant_D_eq g
        (open_interval (pos_Rl (cons_ORlist lf lg) i)
          (pos_Rl (cons_ORlist lf lg) (S i))) l).
  intros; elim H11; clear H11; intros; assert (H12 := H11);
    assert
      (Hyp_cons :
        exists r : R, (exists r0 : Rlist, cons_ORlist lf lg = cons r r0)).
  apply RList_P19; red in |- *; intro; rewrite H13 in H8; elim (lt_n_O _ H8).
  elim Hyp_cons; clear Hyp_cons; intros r [r0 Hyp_cons]; rewrite Hyp_cons;
    unfold FF in |- *; rewrite RList_P12.
  change (g x = g (pos_Rl (mid_Rlist (cons r r0) r) (S i))) in |- *;
    rewrite <- Hyp_cons; rewrite RList_P13.
  assert (H13 := RList_P2 _ _ H _ H8); elim H13; intro.
  unfold constant_D_eq, open_interval in H11, H12; rewrite (H11 x H10);
    assert
      (H15 :
        pos_Rl (cons_ORlist lf lg) i <
        (pos_Rl (cons_ORlist lf lg) i + pos_Rl (cons_ORlist lf lg) (S i)) / 2 <
        pos_Rl (cons_ORlist lf lg) (S i)).
  split.
  apply Rmult_lt_reg_l with 2;
    [ prove_sup0
      | unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
        rewrite <- Rinv_r_sym;
          [ rewrite Rmult_1_l; rewrite double; apply Rplus_lt_compat_l; assumption
            | discrR ] ].
  apply Rmult_lt_reg_l with 2;
    [ prove_sup0
      | unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
        rewrite <- Rinv_r_sym;
          [ rewrite Rmult_1_l; rewrite double;
            rewrite (Rplus_comm (pos_Rl (cons_ORlist lf lg) i));
              apply Rplus_lt_compat_l; assumption
            | discrR ] ].
  rewrite (H11 _ H15); reflexivity.
  elim H10; intros; rewrite H14 in H15;
    elim (Rlt_irrefl _ (Rlt_trans _ _ _ H16 H15)).
  apply H8.
  rewrite RList_P14; rewrite Hyp_cons in H8; simpl in H8; apply H8.
  assert (H11 : a < b).
  apply Rle_lt_trans with (pos_Rl (cons_ORlist lf lg) i).
  rewrite <- H6; rewrite <- (RList_P15 lf lg); try assumption.
  elim (RList_P6 (cons_ORlist lf lg)); intros; apply H11.
  apply RList_P2; assumption.
  apply le_O_n.
  apply lt_trans with (pred (Rlength (cons_ORlist lf lg)));
    [ assumption
      | apply lt_pred_n_n; apply neq_O_lt; red in |- *; intro;
        rewrite <- H13 in H8; elim (lt_n_O _ H8) ].
  rewrite H1; assumption.
  apply Rlt_le_trans with (pos_Rl (cons_ORlist lf lg) (S i)).
  elim H10; intros; apply Rlt_trans with x; assumption.
  rewrite <- H5; rewrite <- (RList_P16 lf lg); try assumption.
  elim (RList_P6 (cons_ORlist lf lg)); intros; apply H11.
  apply RList_P2; assumption.
  apply lt_n_Sm_le; apply lt_n_S; assumption.
  apply lt_pred_n_n; apply neq_O_lt; red in |- *; intro; rewrite <- H13 in H8;
    elim (lt_n_O _ H8).
  rewrite H0; assumption.
  set
    (I :=
      fun j:nat =>
        pos_Rl lg j <= pos_Rl (cons_ORlist lf lg) i /\ (j < Rlength lg)%nat);
    assert (H12 : Nbound I).
  unfold Nbound in |- *; exists (Rlength lg); intros; unfold I in H12; elim H12;
    intros; apply lt_le_weak; assumption.
  assert (H13 :  exists n : nat, I n).
  exists 0%nat; unfold I in |- *; split.
  apply Rle_trans with (pos_Rl (cons_ORlist lf lg) 0).
  right; symmetry  in |- *; rewrite H1; rewrite <- H6; apply RList_P15;
    try assumption; rewrite H1; assumption.
  elim (RList_P6 (cons_ORlist lf lg)); intros; apply H13;
    [ apply RList_P2; assumption
      | apply le_O_n
      | apply lt_trans with (pred (Rlength (cons_ORlist lf lg)));
        [ assumption
          | apply lt_pred_n_n; apply neq_O_lt; red in |- *; intro;
            rewrite <- H15 in H8; elim (lt_n_O _ H8) ] ].
  apply neq_O_lt; red in |- *; intro; rewrite <- H13 in H0;
    rewrite <- H1 in H11; rewrite <- H0 in H11; elim (Rlt_irrefl _ H11).
  assert (H14 := Nzorn H13 H12); elim H14; clear H14; intros x0 H14;
    exists (pos_Rl lg0 x0); unfold constant_D_eq, open_interval in |- *;
      intros; assert (H16 := H4 x0); assert (H17 : (x0 < pred (Rlength lg))%nat).
  elim H14; clear H14; intros; unfold I in H14; elim H14; clear H14; intros;
    apply lt_S_n; replace (S (pred (Rlength lg))) with (Rlength lg).
  inversion H18.
  2: apply lt_n_S; assumption.
  cut (x0 = pred (Rlength lg)).
  intro; rewrite H19 in H14; rewrite H0 in H14;
    cut (pos_Rl (cons_ORlist lf lg) i < b).
  intro; elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H14 H21)).
  apply Rlt_le_trans with (pos_Rl (cons_ORlist lf lg) (S i)).
  elim H10; intros; apply Rlt_trans with x; assumption.
  rewrite <- H0;
    apply Rle_trans with
      (pos_Rl (cons_ORlist lf lg) (pred (Rlength (cons_ORlist lf lg)))).
  elim (RList_P6 (cons_ORlist lf lg)); intros; apply H21.
  apply RList_P2; assumption.
  apply lt_n_Sm_le; apply lt_n_S; assumption.
  apply lt_pred_n_n; apply neq_O_lt; red in |- *; intro; rewrite <- H23 in H8;
    elim (lt_n_O _ H8).
  right; rewrite H0; rewrite <- H5; apply RList_P16; try assumption.
  rewrite H0; assumption.
  rewrite <- H20; reflexivity.
  apply S_pred with 0%nat; apply neq_O_lt; red in |- *; intro;
    rewrite <- H19 in H18; elim (lt_n_O _ H18).
  assert (H18 := H16 H17); unfold constant_D_eq, open_interval in H18;
    rewrite (H18 x1).
  reflexivity.
  elim H15; clear H15; intros; elim H14; clear H14; intros; unfold I in H14;
    elim H14; clear H14; intros; split.
  apply Rle_lt_trans with (pos_Rl (cons_ORlist lf lg) i); assumption.
  apply Rlt_le_trans with (pos_Rl (cons_ORlist lf lg) (S i)); try assumption.
  assert (H22 : (S x0 < Rlength lg)%nat).
  replace (Rlength lg) with (S (pred (Rlength lg))).
  apply lt_n_S; assumption.
  symmetry  in |- *; apply S_pred with 0%nat; apply neq_O_lt; red in |- *;
    intro; rewrite <- H22 in H21; elim (lt_n_O _ H21).
  elim (Rle_dec (pos_Rl lg (S x0)) (pos_Rl (cons_ORlist lf lg) i)); intro.
  assert (H23 : (S x0 <= x0)%nat);
    [ apply H20; unfold I in |- *; split; assumption | elim (le_Sn_n _ H23) ].
  assert (H23 : pos_Rl (cons_ORlist lf lg) i < pos_Rl lg (S x0)).
  auto with real.
  clear b0; apply RList_P17; try assumption;
    [ apply RList_P2; assumption
      | elim (RList_P9 lf lg (pos_Rl lg (S x0))); intros; apply H25; right;
        elim (RList_P3 lg (pos_Rl lg (S x0))); intros;
          apply H27; exists (S x0); split; [ reflexivity | apply H22 ] ].
Qed.

Lemma StepFun_P25 :
  forall (a b:R) (f g:R -> R) (lf lg:Rlist),
    is_subdivision f a b lf ->
    is_subdivision g a b lg -> is_subdivision g a b (cons_ORlist lf lg).
Proof.
  intros a b f g lf lg H H0; case (Rle_dec a b); intro;
    [ apply StepFun_P24 with f; assumption
      | apply StepFun_P5; apply StepFun_P24 with f;
        [ auto with real
          | apply StepFun_P5; assumption
          | apply StepFun_P5; assumption ] ].
Qed.

Lemma StepFun_P26 :
  forall (a b l:R) (f g:R -> R) (l1:Rlist),
    is_subdivision f a b l1 ->
    is_subdivision g a b l1 ->
    is_subdivision (fun x:R => f x + l * g x) a b l1.
Proof.
  intros a b l f g l1 (x0,(H0,(H1,(H2,(H3,H4)))))
    (x,(_,(_,(_,(_,H9))))).
  exists (FF l1 (fun x:R => f x + l * g x)); repeat split; try assumption.
  apply StepFun_P20; rewrite H3; auto with arith.
  intros i H8 x1 H10; unfold open_interval in H10, H9, H4;
    rewrite (H9 _ H8 _ H10); rewrite (H4 _ H8 _ H10);
      assert (H11 : l1 <> nil).
  red in |- *; intro H11; rewrite H11 in H8; elim (lt_n_O _ H8).
  destruct (RList_P19 _ H11) as (r,(r0,H12));
    rewrite H12; unfold FF in |- *;
      change
        (pos_Rl x0 i + l * pos_Rl x i =
          pos_Rl
          (app_Rlist (mid_Rlist (cons r r0) r) (fun x2:R => f x2 + l * g x2))
          (S i)) in |- *; rewrite RList_P12.
  rewrite RList_P13.
  rewrite <- H12; rewrite (H9 _ H8); try rewrite (H4 _ H8);
    reflexivity ||
      (elim H10; clear H10; intros; split;
        [ apply Rmult_lt_reg_l with 2;
          [ prove_sup0
            | unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2));
              rewrite <- Rmult_assoc; rewrite <- Rinv_r_sym;
                [ rewrite Rmult_1_l; rewrite double; apply Rplus_lt_compat_l;
                  apply Rlt_trans with x1; assumption
                  | discrR ] ]
          | apply Rmult_lt_reg_l with 2;
            [ prove_sup0
              | unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2));
                rewrite <- Rmult_assoc; rewrite <- Rinv_r_sym;
                  [ rewrite Rmult_1_l; rewrite double;
                    rewrite (Rplus_comm (pos_Rl l1 i)); apply Rplus_lt_compat_l;
                      apply Rlt_trans with x1; assumption
                    | discrR ] ] ]).
  rewrite <- H12; assumption.
  rewrite RList_P14; simpl in |- *; rewrite H12 in H8; simpl in H8;
    apply lt_n_S; apply H8.
Qed.

Lemma StepFun_P27 :
  forall (a b l:R) (f g:R -> R) (lf lg:Rlist),
    is_subdivision f a b lf ->
    is_subdivision g a b lg ->
    is_subdivision (fun x:R => f x + l * g x) a b (cons_ORlist lf lg).
Proof.
  intros a b l f g lf lg H H0; apply StepFun_P26;
    [ apply StepFun_P23 with g; assumption
      | apply StepFun_P25 with f; assumption ].
Qed.

(** The set of step functions on [a,b] is a vectorial space *)
Lemma StepFun_P28 :
  forall (a b l:R) (f g:StepFun a b), IsStepFun (fun x:R => f x + l * g x) a b.
Proof.
  intros a b l f g; unfold IsStepFun in |- *; assert (H := pre f);
    assert (H0 := pre g); unfold IsStepFun in H, H0; elim H;
      elim H0; intros; apply existT with (cons_ORlist x0 x);
        apply StepFun_P27; assumption.
Qed.

Lemma StepFun_P29 :
  forall (a b:R) (f:StepFun a b), is_subdivision f a b (subdivision f).
Proof.
  intros a b f; unfold is_subdivision in |- *;
    apply existT with (subdivision_val f); apply StepFun_P1.
Qed.

Lemma StepFun_P30 :
  forall (a b l:R) (f g:StepFun a b),
    RiemannInt_SF (mkStepFun (StepFun_P28 l f g)) =
    RiemannInt_SF f + l * RiemannInt_SF g.
Proof.
  intros a b l f g; unfold RiemannInt_SF in |- *; case (Rle_dec a b);
    (intro;
      replace
      (Int_SF (subdivision_val (mkStepFun (StepFun_P28 l f g)))
        (subdivision (mkStepFun (StepFun_P28 l f g)))) with
      (Int_SF
        (FF (cons_ORlist (subdivision f) (subdivision g))
          (fun x:R => f x + l * g x))
        (cons_ORlist (subdivision f) (subdivision g)));
      [ rewrite StepFun_P19;
        replace
        (Int_SF (FF (cons_ORlist (subdivision f) (subdivision g)) f)
          (cons_ORlist (subdivision f) (subdivision g))) with
        (Int_SF (subdivision_val f) (subdivision f));
        [ replace
          (Int_SF (FF (cons_ORlist (subdivision f) (subdivision g)) g)
            (cons_ORlist (subdivision f) (subdivision g))) with
          (Int_SF (subdivision_val g) (subdivision g));
          [ ring
            | apply StepFun_P17 with (fe g) a b;
              [ apply StepFun_P1
                | apply StepFun_P21; apply StepFun_P25 with (fe f);
                  apply StepFun_P29 ] ]
          | apply StepFun_P17 with (fe f) a b;
            [ apply StepFun_P1
              | apply StepFun_P21; apply StepFun_P23 with (fe g);
                apply StepFun_P29 ] ]
        | apply StepFun_P17 with (fun x:R => f x + l * g x) a b;
          [ apply StepFun_P21; apply StepFun_P27; apply StepFun_P29
            | apply (StepFun_P1 (mkStepFun (StepFun_P28 l f g))) ] ]).
Qed.

Lemma StepFun_P31 :
  forall (a b:R) (f:R -> R) (l lf:Rlist),
    adapted_couple f a b l lf ->
    adapted_couple (fun x:R => Rabs (f x)) a b l (app_Rlist lf Rabs).
Proof.
  unfold adapted_couple in |- *; intros; decompose [and] H; clear H;
    repeat split; try assumption.
  symmetry  in |- *; rewrite H3; rewrite RList_P18; reflexivity.
  intros; unfold constant_D_eq, open_interval in |- *;
    unfold constant_D_eq, open_interval in H5; intros;
      rewrite (H5 _ H _ H4); rewrite RList_P12;
        [ reflexivity | rewrite H3 in H; simpl in H; apply H ].
Qed.

Lemma StepFun_P32 :
  forall (a b:R) (f:StepFun a b), IsStepFun (fun x:R => Rabs (f x)) a b.
Proof.
  intros a b f; unfold IsStepFun in |- *; apply existT with (subdivision f);
    unfold is_subdivision in |- *;
      apply existT with (app_Rlist (subdivision_val f) Rabs);
        apply StepFun_P31; apply StepFun_P1.
Qed.

Lemma StepFun_P33 :
  forall l2 l1:Rlist,
    ordered_Rlist l1 -> Rabs (Int_SF l2 l1) <= Int_SF (app_Rlist l2 Rabs) l1.
Proof.
  simple induction l2; intros.
  simpl in |- *; rewrite Rabs_R0; right; reflexivity.
  simpl in |- *; induction  l1 as [| r1 l1 Hrecl1].
  rewrite Rabs_R0; right; reflexivity.
  induction  l1 as [| r2 l1 Hrecl0].
  rewrite Rabs_R0; right; reflexivity.
  apply Rle_trans with (Rabs (r * (r2 - r1)) + Rabs (Int_SF r0 (cons r2 l1))).
  apply Rabs_triang.
  rewrite Rabs_mult; rewrite (Rabs_right (r2 - r1));
    [ apply Rplus_le_compat_l; apply H; apply RList_P4 with r1; assumption
      | apply Rge_minus; apply Rle_ge; apply (H0 0%nat); simpl in |- *;
        apply lt_O_Sn ].
Qed.

Lemma StepFun_P34 :
  forall (a b:R) (f:StepFun a b),
    a <= b ->
    Rabs (RiemannInt_SF f) <= RiemannInt_SF (mkStepFun (StepFun_P32 f)).
Proof.
  intros; unfold RiemannInt_SF in |- *; case (Rle_dec a b); intro.
  replace
  (Int_SF (subdivision_val (mkStepFun (StepFun_P32 f)))
    (subdivision (mkStepFun (StepFun_P32 f)))) with
  (Int_SF (app_Rlist (subdivision_val f) Rabs) (subdivision f)).
  apply StepFun_P33; assert (H0 := StepFun_P29 f); unfold is_subdivision in H0;
    elim H0; intros; unfold adapted_couple in p; decompose [and] p;
      assumption.
  apply StepFun_P17 with (fun x:R => Rabs (f x)) a b;
    [ apply StepFun_P31; apply StepFun_P1
      | apply (StepFun_P1 (mkStepFun (StepFun_P32 f))) ].
  elim n; assumption.
Qed.

Lemma StepFun_P35 :
  forall (l:Rlist) (a b:R) (f g:R -> R),
    ordered_Rlist l ->
    pos_Rl l 0 = a ->
    pos_Rl l (pred (Rlength l)) = b ->
    (forall x:R, a < x < b -> f x <= g x) ->
    Int_SF (FF l f) l <= Int_SF (FF l g) l.
Proof.
  simple induction l; intros.
  right; reflexivity.
  simpl in |- *; induction  r0 as [| r0 r1 Hrecr0].
  right; reflexivity.
  simpl in |- *; apply Rplus_le_compat.
  case (Req_dec r r0); intro.
  rewrite H4; right; ring.
  do 2 rewrite <- (Rmult_comm (r0 - r)); apply Rmult_le_compat_l.
  apply Rge_le; apply Rge_minus; apply Rle_ge; apply (H0 0%nat); simpl in |- *;
    apply lt_O_Sn.
  apply H3; split.
  apply Rmult_lt_reg_l with 2.
  prove_sup0.
  unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
    rewrite <- Rinv_r_sym.
  assert (H5 : r = a).
  apply H1.
  rewrite H5; rewrite Rmult_1_l; rewrite double; apply Rplus_lt_compat_l.
  assert (H6 := H0 0%nat (lt_O_Sn _)).
  simpl in H6.
  elim H6; intro.
  rewrite H5 in H7; apply H7.
  elim H4; assumption.
  discrR.
  apply Rmult_lt_reg_l with 2.
  prove_sup0.
  unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
    rewrite <- Rinv_r_sym.
  rewrite Rmult_1_l; rewrite double; assert (H5 : r0 <= b).
  replace b with
  (pos_Rl (cons r (cons r0 r1)) (pred (Rlength (cons r (cons r0 r1))))).
  replace r0 with (pos_Rl (cons r (cons r0 r1)) 1).
  elim (RList_P6 (cons r (cons r0 r1))); intros; apply H5.
  assumption.
  simpl in |- *; apply le_n_S.
  apply le_O_n.
  simpl in |- *; apply lt_n_Sn.
  reflexivity.
  apply Rle_lt_trans with (r + b).
  apply Rplus_le_compat_l; assumption.
  rewrite (Rplus_comm r); apply Rplus_lt_compat_l.
  apply Rlt_le_trans with r0.
  assert (H6 := H0 0%nat (lt_O_Sn _)).
  simpl in H6.
  elim H6; intro.
  apply H7.
  elim H4; assumption.
  assumption.
  discrR.
  simpl in H; apply H with r0 b.
  apply RList_P4 with r; assumption.
  reflexivity.
  rewrite <- H2; reflexivity.
  intros; apply H3; elim H4; intros; split; try assumption.
  apply Rle_lt_trans with r0; try assumption.
  rewrite <- H1.
  simpl in |- *; apply (H0 0%nat); simpl in |- *; apply lt_O_Sn.
Qed.

Lemma StepFun_P36 :
  forall (a b:R) (f g:StepFun a b) (l:Rlist),
    a <= b ->
    is_subdivision f a b l ->
    is_subdivision g a b l ->
    (forall x:R, a < x < b -> f x <= g x) ->
    RiemannInt_SF f <= RiemannInt_SF g.
Proof.
  intros; unfold RiemannInt_SF in |- *; case (Rle_dec a b); intro.
  replace (Int_SF (subdivision_val f) (subdivision f)) with (Int_SF (FF l f) l).
  replace (Int_SF (subdivision_val g) (subdivision g)) with (Int_SF (FF l g) l).
  unfold is_subdivision in X; elim X; clear X; intros;
    unfold adapted_couple in p; decompose [and] p; clear p;
      assert (H5 : Rmin a b = a);
        [ unfold Rmin in |- *; case (Rle_dec a b); intro;
          [ reflexivity | elim n; assumption ]
          | assert (H7 : Rmax a b = b);
            [ unfold Rmax in |- *; case (Rle_dec a b); intro;
              [ reflexivity | elim n; assumption ]
              | rewrite H5 in H3; rewrite H7 in H2; eapply StepFun_P35 with a b;
                assumption ] ].
  apply StepFun_P17 with (fe g) a b;
    [ apply StepFun_P21; assumption | apply StepFun_P1 ].
  apply StepFun_P17 with (fe f) a b;
    [ apply StepFun_P21; assumption | apply StepFun_P1 ].
  elim n; assumption.
Qed.

Lemma StepFun_P37 :
  forall (a b:R) (f g:StepFun a b),
    a <= b ->
    (forall x:R, a < x < b -> f x <= g x) ->
    RiemannInt_SF f <= RiemannInt_SF g.
Proof.
  intros; eapply StepFun_P36; try assumption.
  eapply StepFun_P25; apply StepFun_P29.
  eapply StepFun_P23; apply StepFun_P29.
Qed.

Lemma StepFun_P38 :
  forall (l:Rlist) (a b:R) (f:R -> R),
    ordered_Rlist l ->
    pos_Rl l 0 = a ->
    pos_Rl l (pred (Rlength l)) = b ->
    { g:StepFun a b |
      g b = f b /\
      (forall i:nat,
        (i < pred (Rlength l))%nat ->
        constant_D_eq g (co_interval (pos_Rl l i) (pos_Rl l (S i)))
        (f (pos_Rl l i))) }.
Proof.
  intros l a b f; generalize a; clear a; induction l.
  intros a H H0 H1; simpl in H0; simpl in H1;
    exists (mkStepFun (StepFun_P4 a b (f b))); split.
  reflexivity.
  intros; elim (lt_n_O _ H2).
  intros; destruct l as [| r1 l].
  simpl in H1; simpl in H0; exists (mkStepFun (StepFun_P4 a b (f b))); split.
  reflexivity.
  intros i H2; elim (lt_n_O _ H2).
  intros; assert (H2 : ordered_Rlist (cons r1 l)).
  apply RList_P4 with r; assumption.
  assert (H3 : pos_Rl (cons r1 l) 0 = r1).
  reflexivity.
  assert (H4 : pos_Rl (cons r1 l) (pred (Rlength (cons r1 l))) = b).
  rewrite <- H1; reflexivity.
  elim (IHl r1 H2 H3 H4); intros g [H5 H6].
  set
    (g' :=
      fun x:R => match Rle_dec r1 x with
                   | left _ => g x
                   | right _ => f a
                 end).
  assert (H7 : r1 <= b).
  rewrite <- H4; apply RList_P7; [ assumption | left; reflexivity ].
  assert (H8 : IsStepFun g' a b).
  unfold IsStepFun in |- *; assert (H8 := pre g); unfold IsStepFun in H8;
    elim H8; intros lg H9; unfold is_subdivision in H9;
      elim H9; clear H9; intros lg2 H9; split with (cons a lg);
        unfold is_subdivision in |- *; split with (cons (f a) lg2);
          unfold adapted_couple in H9; decompose [and] H9; clear H9;
            unfold adapted_couple in |- *; repeat split.
  unfold ordered_Rlist in |- *; intros; simpl in H9;
    induction  i as [| i Hreci].
  simpl in |- *; rewrite H12; replace (Rmin r1 b) with r1.
  simpl in H0; rewrite <- H0; apply (H 0%nat); simpl in |- *; apply lt_O_Sn.
  unfold Rmin in |- *; case (Rle_dec r1 b); intro;
    [ reflexivity | elim n; assumption ].
  apply (H10 i); apply lt_S_n.
  replace (S (pred (Rlength lg))) with (Rlength lg).
  apply H9.
  apply S_pred with 0%nat; apply neq_O_lt; intro; rewrite <- H14 in H9;
    elim (lt_n_O _ H9).
  simpl in |- *; assert (H14 : a <= b).
  rewrite <- H1; simpl in H0; rewrite <- H0; apply RList_P7;
    [ assumption | left; reflexivity ].
  unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; assumption ].
  assert (H14 : a <= b).
  rewrite <- H1; simpl in H0; rewrite <- H0; apply RList_P7;
    [ assumption | left; reflexivity ].
  replace (Rmax a b) with (Rmax r1 b).
  rewrite <- H11; induction  lg as [| r0 lg Hreclg].
  simpl in H13; discriminate.
  reflexivity.
  unfold Rmax in |- *; case (Rle_dec a b); case (Rle_dec r1 b); intros;
    reflexivity || elim n; assumption.
  simpl in |- *; rewrite H13; reflexivity.
  intros; simpl in H9; induction  i as [| i Hreci].
  unfold constant_D_eq, open_interval in |- *; simpl in |- *; intros;
    assert (H16 : Rmin r1 b = r1).
  unfold Rmin in |- *; case (Rle_dec r1 b); intro;
    [ reflexivity | elim n; assumption ].
  rewrite H16 in H12; rewrite H12 in H14; elim H14; clear H14; intros _ H14;
    unfold g' in |- *; case (Rle_dec r1 x); intro r3.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ r3 H14)).
  reflexivity.
  change
    (constant_D_eq g' (open_interval (pos_Rl lg i) (pos_Rl lg (S i)))
      (pos_Rl lg2 i)) in |- *; clear Hreci; assert (H16 := H15 i);
    assert (H17 : (i < pred (Rlength lg))%nat).
  apply lt_S_n.
  replace (S (pred (Rlength lg))) with (Rlength lg).
  assumption.
  apply S_pred with 0%nat; apply neq_O_lt; red in |- *; intro;
    rewrite <- H14 in H9; elim (lt_n_O _ H9).
  assert (H18 := H16 H17); unfold constant_D_eq, open_interval in H18;
    unfold constant_D_eq, open_interval in |- *; intros;
      assert (H19 := H18 _ H14); rewrite <- H19; unfold g' in |- *;
        case (Rle_dec r1 x); intro.
  reflexivity.
  elim n; replace r1 with (Rmin r1 b).
  rewrite <- H12; elim H14; clear H14; intros H14 _; left;
    apply Rle_lt_trans with (pos_Rl lg i); try assumption.
  apply RList_P5.
  assumption.
  elim (RList_P3 lg (pos_Rl lg i)); intros; apply H21; exists i; split.
  reflexivity.
  apply lt_trans with (pred (Rlength lg)); try assumption.
  apply lt_pred_n_n; apply neq_O_lt; red in |- *; intro; rewrite <- H22 in H17;
    elim (lt_n_O _ H17).
  unfold Rmin in |- *; case (Rle_dec r1 b); intro;
    [ reflexivity | elim n0; assumption ].
  exists (mkStepFun H8); split.
  simpl in |- *; unfold g' in |- *; case (Rle_dec r1 b); intro.
  assumption.
  elim n; assumption.
  intros; simpl in H9; induction  i as [| i Hreci].
  unfold constant_D_eq, co_interval in |- *; simpl in |- *; intros; simpl in H0;
    rewrite H0; elim H10; clear H10; intros; unfold g' in |- *;
      case (Rle_dec r1 x); intro r3.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ r3 H11)).
  reflexivity.
  clear Hreci;
    change
      (constant_D_eq (mkStepFun H8)
        (co_interval (pos_Rl (cons r1 l) i) (pos_Rl (cons r1 l) (S i)))
        (f (pos_Rl (cons r1 l) i))) in |- *; assert (H10 := H6 i);
      assert (H11 : (i < pred (Rlength (cons r1 l)))%nat).
  simpl in |- *; apply lt_S_n; assumption.
  assert (H12 := H10 H11); unfold constant_D_eq, co_interval in H12;
    unfold constant_D_eq, co_interval in |- *; intros;
      rewrite <- (H12 _ H13); simpl in |- *; unfold g' in |- *;
        case (Rle_dec r1 x); intro.
  reflexivity.
  elim n; elim H13; clear H13; intros;
    apply Rle_trans with (pos_Rl (cons r1 l) i); try assumption;
      change (pos_Rl (cons r1 l) 0 <= pos_Rl (cons r1 l) i) in |- *;
        elim (RList_P6 (cons r1 l)); intros; apply H15;
          [ assumption
            | apply le_O_n
            | simpl in |- *; apply lt_trans with (Rlength l);
              [ apply lt_S_n; assumption | apply lt_n_Sn ] ].
Qed.

Lemma StepFun_P39 :
  forall (a b:R) (f:StepFun a b),
    RiemannInt_SF f = - RiemannInt_SF (mkStepFun (StepFun_P6 (pre f))).
Proof.
  intros; unfold RiemannInt_SF in |- *; case (Rle_dec a b); case (Rle_dec b a);
    intros.
  assert (H : adapted_couple f a b (subdivision f) (subdivision_val f));
    [ apply StepFun_P1
      | assert
        (H0 :
          adapted_couple (mkStepFun (StepFun_P6 (pre f))) b a
          (subdivision (mkStepFun (StepFun_P6 (pre f))))
          (subdivision_val (mkStepFun (StepFun_P6 (pre f)))));
        [ apply StepFun_P1
          | assert (H1 : a = b);
            [ apply Rle_antisym; assumption
              | rewrite (StepFun_P8 H H1); assert (H2 : b = a);
                [ symmetry  in |- *; apply H1 | rewrite (StepFun_P8 H0 H2); ring ] ] ] ].
  rewrite Ropp_involutive; eapply StepFun_P17;
    [ apply StepFun_P1
      | apply StepFun_P2; set (H := StepFun_P6 (pre f)); unfold IsStepFun in H;
        elim H; intros; unfold is_subdivision in |- *;
          elim p; intros; apply p0 ].
  apply Ropp_eq_compat; eapply StepFun_P17;
    [ apply StepFun_P1
      | apply StepFun_P2; set (H := StepFun_P6 (pre f)); unfold IsStepFun in H;
        elim H; intros; unfold is_subdivision in |- *;
          elim p; intros; apply p0 ].
  assert (H : a < b);
    [ auto with real
      | assert (H0 : b < a);
        [ auto with real | elim (Rlt_irrefl _ (Rlt_trans _ _ _ H H0)) ] ].
Qed.

Lemma StepFun_P40 :
  forall (f:R -> R) (a b c:R) (l1 l2 lf1 lf2:Rlist),
    a < b ->
    b < c ->
    adapted_couple f a b l1 lf1 ->
    adapted_couple f b c l2 lf2 ->
    adapted_couple f a c (cons_Rlist l1 l2) (FF (cons_Rlist l1 l2) f).
Proof.
  intros f a b c l1 l2 lf1 lf2 H H0 H1 H2; unfold adapted_couple in H1, H2;
    unfold adapted_couple in |- *; decompose [and] H1;
      decompose [and] H2; clear H1 H2; repeat split.
  apply RList_P25; try assumption.
  rewrite H10; rewrite H4; unfold Rmin, Rmax in |- *; case (Rle_dec a b);
    case (Rle_dec b c); intros;
      (right; reflexivity) || (elim n; left; assumption).
  rewrite RList_P22.
  rewrite H5; unfold Rmin, Rmax in |- *; case (Rle_dec a b); case (Rle_dec a c);
    intros;
      [ reflexivity
        | elim n; apply Rle_trans with b; left; assumption
        | elim n; left; assumption
        | elim n0; left; assumption ].
  red in |- *; intro; rewrite H1 in H6; discriminate.
  rewrite RList_P24.
  rewrite H9; unfold Rmin, Rmax in |- *; case (Rle_dec b c); case (Rle_dec a c);
    intros;
      [ reflexivity
        | elim n; apply Rle_trans with b; left; assumption
        | elim n; left; assumption
        | elim n0; left; assumption ].
  red in |- *; intro; rewrite H1 in H11; discriminate.
  apply StepFun_P20.
  rewrite RList_P23; apply neq_O_lt; red in |- *; intro.
  assert (H2 : (Rlength l1 + Rlength l2)%nat = 0%nat).
  symmetry  in |- *; apply H1.
  elim (plus_is_O _ _ H2); intros; rewrite H12 in H6; discriminate.
  unfold constant_D_eq, open_interval in |- *; intros;
    elim (le_or_lt (S (S i)) (Rlength l1)); intro.
  assert (H14 : pos_Rl (cons_Rlist l1 l2) i = pos_Rl l1 i).
  apply RList_P26; apply lt_S_n; apply le_lt_n_Sm; apply le_S_n;
    apply le_trans with (Rlength l1); [ assumption | apply le_n_Sn ].
  assert (H15 : pos_Rl (cons_Rlist l1 l2) (S i) = pos_Rl l1 (S i)).
  apply RList_P26; apply lt_S_n; apply le_lt_n_Sm; assumption.
  rewrite H14 in H2; rewrite H15 in H2; assert (H16 : (2 <= Rlength l1)%nat).
  apply le_trans with (S (S i));
    [ repeat apply le_n_S; apply le_O_n | assumption ].
  elim (RList_P20 _ H16); intros r1 [r2 [r3 H17]]; rewrite H17;
    change
      (f x = pos_Rl (app_Rlist (mid_Rlist (cons_Rlist (cons r2 r3) l2) r1) f) i)
      in |- *; rewrite RList_P12.
  induction  i as [| i Hreci].
  simpl in |- *; assert (H18 := H8 0%nat);
    unfold constant_D_eq, open_interval in H18;
      assert (H19 : (0 < pred (Rlength l1))%nat).
  rewrite H17; simpl in |- *; apply lt_O_Sn.
  assert (H20 := H18 H19); repeat rewrite H20.
  reflexivity.
  assert (H21 : r1 <= r2).
  rewrite H17 in H3; apply (H3 0%nat).
  simpl in |- *; apply lt_O_Sn.
  elim H21; intro.
  split.
  rewrite H17; simpl in |- *; apply Rmult_lt_reg_l with 2;
    [ prove_sup0
      | unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
        rewrite <- Rinv_r_sym;
          [ rewrite Rmult_1_l; rewrite double; apply Rplus_lt_compat_l; assumption
            | discrR ] ].
  rewrite H17; simpl in |- *; apply Rmult_lt_reg_l with 2;
    [ prove_sup0
      | unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
        rewrite <- Rinv_r_sym;
          [ rewrite Rmult_1_l; rewrite (Rplus_comm r1); rewrite double;
            apply Rplus_lt_compat_l; assumption
            | discrR ] ].
  elim H2; intros; rewrite H17 in H23; rewrite H17 in H24; simpl in H24;
    simpl in H23; rewrite H22 in H23;
      elim (Rlt_irrefl _ (Rlt_trans _ _ _ H23 H24)).
  assumption.
  clear Hreci; rewrite RList_P13.
  rewrite H17 in H14; rewrite H17 in H15;
    change
      (pos_Rl (cons_Rlist (cons r2 r3) l2) i =
        pos_Rl (cons r1 (cons r2 r3)) (S i)) in H14; rewrite H14;
      change
        (pos_Rl (cons_Rlist (cons r2 r3) l2) (S i) =
          pos_Rl (cons r1 (cons r2 r3)) (S (S i))) in H15;
        rewrite H15; assert (H18 := H8 (S i));
          unfold constant_D_eq, open_interval in H18;
            assert (H19 : (S i < pred (Rlength l1))%nat).
  apply lt_pred; apply lt_S_n; apply le_lt_n_Sm; assumption.
  assert (H20 := H18 H19); repeat rewrite H20.
  reflexivity.
  rewrite <- H17; assert (H21 : pos_Rl l1 (S i) <= pos_Rl l1 (S (S i))).
  apply (H3 (S i)); apply lt_pred; apply lt_S_n; apply le_lt_n_Sm; assumption.
  elim H21; intro.
  split.
  apply Rmult_lt_reg_l with 2;
    [ prove_sup0
      | unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
        rewrite <- Rinv_r_sym;
          [ rewrite Rmult_1_l; rewrite double; apply Rplus_lt_compat_l; assumption
            | discrR ] ].
  apply Rmult_lt_reg_l with 2;
    [ prove_sup0
      | unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
        rewrite <- Rinv_r_sym;
          [ rewrite Rmult_1_l; rewrite (Rplus_comm (pos_Rl l1 (S i)));
            rewrite double; apply Rplus_lt_compat_l; assumption
            | discrR ] ].
  elim H2; intros; rewrite H22 in H23;
    elim (Rlt_irrefl _ (Rlt_trans _ _ _ H23 H24)).
  assumption.
  simpl in |- *; rewrite H17 in H1; simpl in H1; apply lt_S_n; assumption.
  rewrite RList_P14; rewrite H17 in H1; simpl in H1; apply H1.
  inversion H12.
  assert (H16 : pos_Rl (cons_Rlist l1 l2) (S i) = b).
  rewrite RList_P29.
  rewrite H15; rewrite <- minus_n_n; rewrite H10; unfold Rmin in |- *;
    case (Rle_dec b c); intro; [ reflexivity | elim n; left; assumption ].
  rewrite H15; apply le_n.
  induction  l1 as [| r l1 Hrecl1].
  simpl in H15; discriminate.
  clear Hrecl1; simpl in H1; simpl in |- *; apply lt_n_S; assumption.
  assert (H17 : pos_Rl (cons_Rlist l1 l2) i = b).
  rewrite RList_P26.
  replace i with (pred (Rlength l1));
  [ rewrite H4; unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; left; assumption ]
    | rewrite H15; reflexivity ].
  rewrite H15; apply lt_n_Sn.
  rewrite H16 in H2; rewrite H17 in H2; elim H2; intros;
    elim (Rlt_irrefl _ (Rlt_trans _ _ _ H14 H18)).
  assert (H16 : pos_Rl (cons_Rlist l1 l2) i = pos_Rl l2 (i - Rlength l1)).
  apply RList_P29.
  apply le_S_n; assumption.
  apply lt_le_trans with (pred (Rlength (cons_Rlist l1 l2)));
    [ assumption | apply le_pred_n ].
  assert
    (H17 : pos_Rl (cons_Rlist l1 l2) (S i) = pos_Rl l2 (S (i - Rlength l1))).
  replace (S (i - Rlength l1)) with (S i - Rlength l1)%nat.
  apply RList_P29.
  apply le_S_n; apply le_trans with (S i); [ assumption | apply le_n_Sn ].
  induction  l1 as [| r l1 Hrecl1].
  simpl in H6; discriminate.
  clear Hrecl1; simpl in H1; simpl in |- *; apply lt_n_S; assumption.
  symmetry  in |- *; apply minus_Sn_m; apply le_S_n; assumption.
  assert (H18 : (2 <= Rlength l1)%nat).
  clear f c l2 lf2 H0 H3 H8 H7 H10 H9 H11 H13 i H1 x H2 H12 m H14 H15 H16 H17;
    induction  l1 as [| r l1 Hrecl1].
  discriminate.
  clear Hrecl1; induction  l1 as [| r0 l1 Hrecl1].
  simpl in H5; simpl in H4; assert (H0 : Rmin a b < Rmax a b).
  unfold Rmin, Rmax in |- *; case (Rle_dec a b); intro;
    [ assumption | elim n; left; assumption ].
  rewrite <- H5 in H0; rewrite <- H4 in H0; elim (Rlt_irrefl _ H0).
  clear Hrecl1; simpl in |- *; repeat apply le_n_S; apply le_O_n.
  elim (RList_P20 _ H18); intros r1 [r2 [r3 H19]]; rewrite H19;
    change
      (f x = pos_Rl (app_Rlist (mid_Rlist (cons_Rlist (cons r2 r3) l2) r1) f) i)
      in |- *; rewrite RList_P12.
  induction  i as [| i Hreci].
  assert (H20 := le_S_n _ _ H15); assert (H21 := le_trans _ _ _ H18 H20);
    elim (le_Sn_O _ H21).
  clear Hreci; rewrite RList_P13.
  rewrite H19 in H16; rewrite H19 in H17;
    change
      (pos_Rl (cons_Rlist (cons r2 r3) l2) i =
        pos_Rl l2 (S i - Rlength (cons r1 (cons r2 r3))))
      in H16; rewrite H16;
        change
          (pos_Rl (cons_Rlist (cons r2 r3) l2) (S i) =
            pos_Rl l2 (S (S i - Rlength (cons r1 (cons r2 r3)))))
          in H17; rewrite H17; assert (H20 := H13 (S i - Rlength l1)%nat);
            unfold constant_D_eq, open_interval in H20;
              assert (H21 : (S i - Rlength l1 < pred (Rlength l2))%nat).
  apply lt_pred; rewrite minus_Sn_m.
  apply plus_lt_reg_l with (Rlength l1); rewrite <- le_plus_minus.
  rewrite H19 in H1; simpl in H1; rewrite H19; simpl in |- *;
    rewrite RList_P23 in H1; apply lt_n_S; assumption.
  apply le_trans with (S i); [ apply le_S_n; assumption | apply le_n_Sn ].
  apply le_S_n; assumption.
  assert (H22 := H20 H21); repeat rewrite H22.
  reflexivity.
  rewrite <- H19;
    assert
      (H23 : pos_Rl l2 (S i - Rlength l1) <= pos_Rl l2 (S (S i - Rlength l1))).
  apply H7; apply lt_pred.
  rewrite minus_Sn_m.
  apply plus_lt_reg_l with (Rlength l1); rewrite <- le_plus_minus.
  rewrite H19 in H1; simpl in H1; rewrite H19; simpl in |- *;
    rewrite RList_P23 in H1; apply lt_n_S; assumption.
  apply le_trans with (S i); [ apply le_S_n; assumption | apply le_n_Sn ].
  apply le_S_n; assumption.
  elim H23; intro.
  split.
  apply Rmult_lt_reg_l with 2;
    [ prove_sup0
      | unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
        rewrite <- Rinv_r_sym;
          [ rewrite Rmult_1_l; rewrite double; apply Rplus_lt_compat_l; assumption
            | discrR ] ].
  apply Rmult_lt_reg_l with 2;
    [ prove_sup0
      | unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
        rewrite <- Rinv_r_sym;
          [ rewrite Rmult_1_l; rewrite (Rplus_comm (pos_Rl l2 (S i - Rlength l1)));
            rewrite double; apply Rplus_lt_compat_l; assumption
            | discrR ] ].
  rewrite <- H19 in H16; rewrite <- H19 in H17; elim H2; intros;
    rewrite H19 in H25; rewrite H19 in H26; simpl in H25;
      simpl in H16; rewrite H16 in H25; simpl in H26; simpl in H17;
        rewrite H17 in H26; simpl in H24; rewrite H24 in H25;
          elim (Rlt_irrefl _ (Rlt_trans _ _ _ H25 H26)).
  assert (H23 : pos_Rl (cons_Rlist l1 l2) (S i) = pos_Rl l2 (S i - Rlength l1)).
  rewrite H19; simpl in |- *; simpl in H16; apply H16.
  assert
    (H24 :
      pos_Rl (cons_Rlist l1 l2) (S (S i)) = pos_Rl l2 (S (S i - Rlength l1))).
  rewrite H19; simpl in |- *; simpl in H17; apply H17.
  rewrite <- H23; rewrite <- H24; assumption.
  simpl in |- *; rewrite H19 in H1; simpl in H1; apply lt_S_n; assumption.
  rewrite RList_P14; rewrite H19 in H1; simpl in H1; simpl in |- *; apply H1.
Qed.

Lemma StepFun_P41 :
  forall (f:R -> R) (a b c:R),
    a <= b -> b <= c -> IsStepFun f a b -> IsStepFun f b c -> IsStepFun f a c.
Proof.
  intros f a b c H H0 (l1,(lf1,H1)) (l2,(lf2,H2));
    destruct (total_order_T a b) as [[Hltab|Hab]|Hgtab].
  destruct (total_order_T b c) as [[Hltbc|Hbc]|Hgtbc].
  exists (cons_Rlist l1 l2); exists (FF (cons_Rlist l1 l2) f);
    apply StepFun_P40 with b lf1 lf2; assumption.
  exists l1; exists lf1; rewrite Hbc in H1; assumption.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H0 Hgtbc)).
  exists l2; exists lf2; rewrite <- Hab in H2; assumption.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H Hgtab)).
Qed.

Lemma StepFun_P42 :
  forall (l1 l2:Rlist) (f:R -> R),
    pos_Rl l1 (pred (Rlength l1)) = pos_Rl l2 0 ->
    Int_SF (FF (cons_Rlist l1 l2) f) (cons_Rlist l1 l2) =
    Int_SF (FF l1 f) l1 + Int_SF (FF l2 f) l2.
Proof.
  intros l1 l2 f; induction l1 as [| r l1 IHl1]; intros H;
    [ simpl in |- *; ring
      | destruct l1 as [| r0 r1];
        [ simpl in H; simpl in |- *; destruct l2 as [| r0 r1];
          [ simpl in |- *; ring | simpl in |- *; simpl in H; rewrite H; ring ]
          | simpl in |- *; rewrite Rplus_assoc; apply Rplus_eq_compat_l; apply IHl1;
            rewrite <- H; reflexivity ] ].
Qed.

Lemma StepFun_P43 :
  forall (f:R -> R) (a b c:R) (pr1:IsStepFun f a b)
    (pr2:IsStepFun f b c) (pr3:IsStepFun f a c),
    RiemannInt_SF (mkStepFun pr1) + RiemannInt_SF (mkStepFun pr2) =
    RiemannInt_SF (mkStepFun pr3).
Proof.
  intros f; intros.
  pose proof pr1 as (l1,(lf1,H1)).
  pose proof pr2 as (l2,(lf2,H2)).
  pose proof pr3 as (l3,(lf3,H3)).
  replace (RiemannInt_SF (mkStepFun pr1)) with
  match Rle_dec a b with
    | left _ => Int_SF lf1 l1
    | right _ => - Int_SF lf1 l1
  end.
  replace (RiemannInt_SF (mkStepFun pr2)) with
  match Rle_dec b c with
    | left _ => Int_SF lf2 l2
    | right _ => - Int_SF lf2 l2
  end.
  replace (RiemannInt_SF (mkStepFun pr3)) with
  match Rle_dec a c with
    | left _ => Int_SF lf3 l3
    | right _ => - Int_SF lf3 l3
  end.
  case (Rle_dec a b); case (Rle_dec b c); case (Rle_dec a c); intros.
  elim r1; intro.
  elim r0; intro.
  replace (Int_SF lf3 l3) with
  (Int_SF (FF (cons_Rlist l1 l2) f) (cons_Rlist l1 l2)).
  replace (Int_SF lf1 l1) with (Int_SF (FF l1 f) l1).
  replace (Int_SF lf2 l2) with (Int_SF (FF l2 f) l2).
  symmetry  in |- *; apply StepFun_P42.
  unfold adapted_couple in H1, H2; decompose [and] H1; decompose [and] H2;
    clear H1 H2; rewrite H11; rewrite H5; unfold Rmax, Rmin in |- *;
      case (Rle_dec a b); case (Rle_dec b c); intros; reflexivity || elim n;
        assumption.
  eapply StepFun_P17;
    [ apply StepFun_P21; unfold is_subdivision in |- *; split with lf2; apply H2;
      assumption
      | assumption ].
  eapply StepFun_P17;
    [ apply StepFun_P21; unfold is_subdivision in |- *; split with lf1; apply H1
      | assumption ].
  eapply StepFun_P17; [ apply (StepFun_P40 H H0 H1 H2) | apply H3 ].
  replace (Int_SF lf2 l2) with 0.
  rewrite Rplus_0_r; eapply StepFun_P17;
    [ apply H1 | rewrite <- H0 in H3; apply H3 ].
  symmetry  in |- *; eapply StepFun_P8; [ apply H2 | assumption ].
  replace (Int_SF lf1 l1) with 0.
  rewrite Rplus_0_l; eapply StepFun_P17;
    [ apply H2 | rewrite H in H3; apply H3 ].
  symmetry  in |- *; eapply StepFun_P8; [ apply H1 | assumption ].
  elim n; apply Rle_trans with b; assumption.
  apply Rplus_eq_reg_l with (Int_SF lf2 l2);
    replace (Int_SF lf2 l2 + (Int_SF lf1 l1 + - Int_SF lf2 l2)) with
    (Int_SF lf1 l1); [ idtac | ring ].
  assert (H : c < b).
  auto with real.
  elim r; intro.
  rewrite Rplus_comm;
    replace (Int_SF lf1 l1) with
    (Int_SF (FF (cons_Rlist l3 l2) f) (cons_Rlist l3 l2)).
  replace (Int_SF lf3 l3) with (Int_SF (FF l3 f) l3).
  replace (Int_SF lf2 l2) with (Int_SF (FF l2 f) l2).
  apply StepFun_P42.
  unfold adapted_couple in H2, H3; decompose [and] H2; decompose [and] H3;
    clear H3 H2; rewrite H10; rewrite H6; unfold Rmax, Rmin in |- *;
      case (Rle_dec a c); case (Rle_dec b c); intros;
        [ elim n; assumption
          | reflexivity
          | elim n0; assumption
          | elim n1; assumption ].
  eapply StepFun_P17;
    [ apply StepFun_P21; unfold is_subdivision in |- *; split with lf2; apply H2
      | assumption ].
  eapply StepFun_P17;
    [ apply StepFun_P21; unfold is_subdivision in |- *; split with lf3; apply H3
      | assumption ].
  eapply StepFun_P17;
    [ apply (StepFun_P40 H0 H H3 (StepFun_P2 H2)) | apply H1 ].
  replace (Int_SF lf3 l3) with 0.
  rewrite Rplus_0_r; eapply StepFun_P17;
    [ apply H1 | apply StepFun_P2; rewrite <- H0 in H2; apply H2 ].
  symmetry  in |- *; eapply StepFun_P8; [ apply H3 | assumption ].
  replace (Int_SF lf2 l2) with (Int_SF lf3 l3 + Int_SF lf1 l1).
  ring.
  elim r; intro.
  replace (Int_SF lf2 l2) with
  (Int_SF (FF (cons_Rlist l3 l1) f) (cons_Rlist l3 l1)).
  replace (Int_SF lf3 l3) with (Int_SF (FF l3 f) l3).
  replace (Int_SF lf1 l1) with (Int_SF (FF l1 f) l1).
  symmetry  in |- *; apply StepFun_P42.
  unfold adapted_couple in H1, H3; decompose [and] H1; decompose [and] H3;
    clear H3 H1; rewrite H9; rewrite H5; unfold Rmax, Rmin in |- *;
      case (Rle_dec a c); case (Rle_dec a b); intros;
        [ elim n; assumption
          | elim n1; assumption
          | reflexivity
          | elim n1; assumption ].
  eapply StepFun_P17;
    [ apply StepFun_P21; unfold is_subdivision in |- *; split with lf1; apply H1
      | assumption ].
  eapply StepFun_P17;
    [ apply StepFun_P21; unfold is_subdivision in |- *; split with lf3; apply H3
      | assumption ].
  eapply StepFun_P17.
  assert (H0 : c < a).
  auto with real.
  apply (StepFun_P40 H0 H (StepFun_P2 H3) H1).
  apply StepFun_P2; apply H2.
  replace (Int_SF lf1 l1) with 0.
  rewrite Rplus_0_r; eapply StepFun_P17;
    [ apply H3 | rewrite <- H in H2; apply H2 ].
  symmetry  in |- *; eapply StepFun_P8; [ apply H1 | assumption ].
  assert (H : b < a).
  auto with real.
  replace (Int_SF lf2 l2) with (Int_SF lf3 l3 + Int_SF lf1 l1).
  ring.
  rewrite Rplus_comm; elim r; intro.
  replace (Int_SF lf2 l2) with
  (Int_SF (FF (cons_Rlist l1 l3) f) (cons_Rlist l1 l3)).
  replace (Int_SF lf3 l3) with (Int_SF (FF l3 f) l3).
  replace (Int_SF lf1 l1) with (Int_SF (FF l1 f) l1).
  symmetry  in |- *; apply StepFun_P42.
  unfold adapted_couple in H1, H3; decompose [and] H1; decompose [and] H3;
    clear H3 H1; rewrite H11; rewrite H5; unfold Rmax, Rmin in |- *;
      case (Rle_dec a c); case (Rle_dec a b); intros;
        [ elim n; assumption
          | reflexivity
          | elim n0; assumption
          | elim n1; assumption ].
  eapply StepFun_P17;
    [ apply StepFun_P21; unfold is_subdivision in |- *; split with lf1; apply H1
      | assumption ].
  eapply StepFun_P17;
    [ apply StepFun_P21; unfold is_subdivision in |- *; split with lf3; apply H3
      | assumption ].
  eapply StepFun_P17.
  apply (StepFun_P40 H H0 (StepFun_P2 H1) H3).
  apply H2.
  replace (Int_SF lf3 l3) with 0.
  rewrite Rplus_0_r; eapply StepFun_P17;
    [ apply H1 | rewrite <- H0 in H2; apply StepFun_P2; apply H2 ].
  symmetry  in |- *; eapply StepFun_P8; [ apply H3 | assumption ].
  assert (H : c < a).
  auto with real.
  replace (Int_SF lf1 l1) with (Int_SF lf2 l2 + Int_SF lf3 l3).
  ring.
  elim r; intro.
  replace (Int_SF lf1 l1) with
  (Int_SF (FF (cons_Rlist l2 l3) f) (cons_Rlist l2 l3)).
  replace (Int_SF lf3 l3) with (Int_SF (FF l3 f) l3).
  replace (Int_SF lf2 l2) with (Int_SF (FF l2 f) l2).
  symmetry  in |- *; apply StepFun_P42.
  unfold adapted_couple in H2, H3; decompose [and] H2; decompose [and] H3;
    clear H3 H2; rewrite H11; rewrite H5; unfold Rmax, Rmin in |- *;
      case (Rle_dec a c); case (Rle_dec b c); intros;
        [ elim n; assumption
          | elim n1; assumption
          | reflexivity
          | elim n1; assumption ].
  eapply StepFun_P17;
    [ apply StepFun_P21; unfold is_subdivision in |- *; split with lf2; apply H2
      | assumption ].
  eapply StepFun_P17;
    [ apply StepFun_P21; unfold is_subdivision in |- *; split with lf3; apply H3
      | assumption ].
  eapply StepFun_P17.
  apply (StepFun_P40 H0 H H2 (StepFun_P2 H3)).
  apply StepFun_P2; apply H1.
  replace (Int_SF lf2 l2) with 0.
  rewrite Rplus_0_l; eapply StepFun_P17;
    [ apply H3 | rewrite H0 in H1; apply H1 ].
  symmetry  in |- *; eapply StepFun_P8; [ apply H2 | assumption ].
  elim n; apply Rle_trans with a; try assumption.
  auto with real.
  assert (H : c < b).
  auto with real.
  assert (H0 : b < a).
  auto with real.
  replace (Int_SF lf3 l3) with (Int_SF lf2 l2 + Int_SF lf1 l1).
  ring.
  replace (Int_SF lf3 l3) with
  (Int_SF (FF (cons_Rlist l2 l1) f) (cons_Rlist l2 l1)).
  replace (Int_SF lf1 l1) with (Int_SF (FF l1 f) l1).
  replace (Int_SF lf2 l2) with (Int_SF (FF l2 f) l2).
  symmetry  in |- *; apply StepFun_P42.
  unfold adapted_couple in H2, H1; decompose [and] H2; decompose [and] H1;
    clear H1 H2; rewrite H11; rewrite H5; unfold Rmax, Rmin in |- *;
      case (Rle_dec a b); case (Rle_dec b c); intros;
        [ elim n1; assumption
          | elim n1; assumption
          | elim n0; assumption
          | reflexivity ].
  eapply StepFun_P17;
    [ apply StepFun_P21; unfold is_subdivision in |- *; split with lf2; apply H2
      | assumption ].
  eapply StepFun_P17;
    [ apply StepFun_P21; unfold is_subdivision in |- *; split with lf1; apply H1
      | assumption ].
  eapply StepFun_P17.
  apply (StepFun_P40 H H0 (StepFun_P2 H2) (StepFun_P2 H1)).
  apply StepFun_P2; apply H3.
  unfold RiemannInt_SF in |- *; case (Rle_dec a c); intro.
  eapply StepFun_P17.
  apply H3.
  change
    (adapted_couple (mkStepFun pr3) a c (subdivision (mkStepFun pr3))
      (subdivision_val (mkStepFun pr3))) in |- *; apply StepFun_P1.
  apply Ropp_eq_compat; eapply StepFun_P17.
  apply H3.
  change
    (adapted_couple (mkStepFun pr3) a c (subdivision (mkStepFun pr3))
      (subdivision_val (mkStepFun pr3))) in |- *; apply StepFun_P1.
  unfold RiemannInt_SF in |- *; case (Rle_dec b c); intro.
  eapply StepFun_P17.
  apply H2.
  change
    (adapted_couple (mkStepFun pr2) b c (subdivision (mkStepFun pr2))
      (subdivision_val (mkStepFun pr2))) in |- *; apply StepFun_P1.
  apply Ropp_eq_compat; eapply StepFun_P17.
  apply H2.
  change
    (adapted_couple (mkStepFun pr2) b c (subdivision (mkStepFun pr2))
      (subdivision_val (mkStepFun pr2))) in |- *; apply StepFun_P1.
  unfold RiemannInt_SF in |- *; case (Rle_dec a b); intro.
  eapply StepFun_P17.
  apply H1.
  change
    (adapted_couple (mkStepFun pr1) a b (subdivision (mkStepFun pr1))
      (subdivision_val (mkStepFun pr1))) in |- *; apply StepFun_P1.
  apply Ropp_eq_compat; eapply StepFun_P17.
  apply H1.
  change
    (adapted_couple (mkStepFun pr1) a b (subdivision (mkStepFun pr1))
      (subdivision_val (mkStepFun pr1))) in |- *; apply StepFun_P1.
Qed.

Lemma StepFun_P44 :
  forall (f:R -> R) (a b c:R),
    IsStepFun f a b -> a <= c <= b -> IsStepFun f a c.
Proof.
  intros f; intros; assert (H0 : a <= b).
  elim H; intros; apply Rle_trans with c; assumption.
  elim H; clear H; intros; unfold IsStepFun in X; unfold is_subdivision in X;
    elim X; clear X; intros l1 [lf1 H2];
      cut
        (forall (l1 lf1:Rlist) (a b c:R) (f:R -> R),
          adapted_couple f a b l1 lf1 ->
          a <= c <= b ->
          { l:Rlist & { l0:Rlist & adapted_couple f a c l l0 } }).
  intro X; unfold IsStepFun in |- *; unfold is_subdivision in |- *; eapply X.
  apply H2.
  split; assumption.
  clear f a b c H0 H H1 H2 l1 lf1; simple induction l1.
  intros; unfold adapted_couple in H; decompose [and] H; clear H; simpl in H4;
    discriminate.
  simple induction r0.
  intros X lf1 a b c f H H0; assert (H1 : a = b).
  unfold adapted_couple in H; decompose [and] H; clear H; simpl in H3;
    simpl in H2; assert (H7 : a <= b).
  elim H0; intros; apply Rle_trans with c; assumption.
  replace a with (Rmin a b).
  pattern b at 2 in |- *; replace b with (Rmax a b).
  rewrite <- H2; rewrite H3; reflexivity.
  unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; assumption ].
  unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; assumption ].
  split with (cons r nil); split with lf1; assert (H2 : c = b).
  rewrite H1 in H0; elim H0; intros; apply Rle_antisym; assumption.
  rewrite H2; assumption.
  intros r1 r2 _ X0 lf1 a b c f H H0; induction  lf1 as [| r3 lf1 Hreclf1].
  unfold adapted_couple in H; decompose [and] H; clear H; simpl in H4;
    discriminate.
  clear Hreclf1; assert (H1 : {c <= r1} + {r1 < c}).
  case (Rle_dec c r1); intro; [ left; assumption | right; auto with real ].
  elim H1; intro.
  split with (cons r (cons c nil)); split with (cons r3 nil);
    unfold adapted_couple in H; decompose [and] H; clear H;
      assert (H6 : r = a).
  simpl in H4; rewrite H4; unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ reflexivity
      | elim n; elim H0; intros; apply Rle_trans with c; assumption ].
  elim H0; clear H0; intros; unfold adapted_couple in |- *; repeat split.
  rewrite H6; unfold ordered_Rlist in |- *; intros; simpl in H8; inversion H8;
    [ simpl in |- *; assumption | elim (le_Sn_O _ H10) ].
  simpl in |- *; unfold Rmin in |- *; case (Rle_dec a c); intro;
    [ assumption | elim n; assumption ].
  simpl in |- *; unfold Rmax in |- *; case (Rle_dec a c); intro;
    [ reflexivity | elim n; assumption ].
  unfold constant_D_eq, open_interval in |- *; intros; simpl in H8;
    inversion H8.
  simpl in |- *; assert (H10 := H7 0%nat);
    assert (H12 : (0 < pred (Rlength (cons r (cons r1 r2))))%nat).
  simpl in |- *; apply lt_O_Sn.
  apply (H10 H12); unfold open_interval in |- *; simpl in |- *;
    rewrite H11 in H9; simpl in H9; elim H9; clear H9;
      intros; split; try assumption.
  apply Rlt_le_trans with c; assumption.
  elim (le_Sn_O _ H11).
  cut (adapted_couple f r1 b (cons r1 r2) lf1).
  cut (r1 <= c <= b).
  intros.
  elim (X0 _ _ _ _ _ H3 H2); intros l1' [lf1' H4]; split with (cons r l1');
    split with (cons r3 lf1'); unfold adapted_couple in H, H4;
      decompose [and] H; decompose [and] H4; clear H H4 X0;
        assert (H14 : a <= b).
  elim H0; intros; apply Rle_trans with c; assumption.
  assert (H16 : r = a).
  simpl in H7; rewrite H7; unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; assumption ].
  induction  l1' as [| r4 l1' Hrecl1'].
  simpl in H13; discriminate.
  clear Hrecl1'; unfold adapted_couple in |- *; repeat split.
  unfold ordered_Rlist in |- *; intros; simpl in H; induction  i as [| i Hreci].
  simpl in |- *; replace r4 with r1.
  apply (H5 0%nat).
  simpl in |- *; apply lt_O_Sn.
  simpl in H12; rewrite H12; unfold Rmin in |- *; case (Rle_dec r1 c); intro;
    [ reflexivity | elim n; left; assumption ].
  apply (H9 i); simpl in |- *; apply lt_S_n; assumption.
  simpl in |- *; unfold Rmin in |- *; case (Rle_dec a c); intro;
    [ assumption | elim n; elim H0; intros; assumption ].
  replace (Rmax a c) with (Rmax r1 c).
  rewrite <- H11; reflexivity.
  unfold Rmax in |- *; case (Rle_dec r1 c); case (Rle_dec a c); intros;
    [ reflexivity
      | elim n; elim H0; intros; assumption
      | elim n; left; assumption
      | elim n0; left; assumption ].
  simpl in |- *; simpl in H13; rewrite H13; reflexivity.
  intros; simpl in H; unfold constant_D_eq, open_interval in |- *; intros;
    induction  i as [| i Hreci].
  simpl in |- *; assert (H17 := H10 0%nat);
    assert (H18 : (0 < pred (Rlength (cons r (cons r1 r2))))%nat).
  simpl in |- *; apply lt_O_Sn.
  apply (H17 H18); unfold open_interval in |- *; simpl in |- *; simpl in H4;
    elim H4; clear H4; intros; split; try assumption;
      replace r1 with r4.
  assumption.
  simpl in H12; rewrite H12; unfold Rmin in |- *; case (Rle_dec r1 c); intro;
    [ reflexivity | elim n; left; assumption ].
  clear Hreci; simpl in |- *; apply H15.
  simpl in |- *; apply lt_S_n; assumption.
  unfold open_interval in |- *; apply H4.
  split.
  left; assumption.
  elim H0; intros; assumption.
  eapply StepFun_P7;
    [ elim H0; intros; apply Rle_trans with c; [ apply H2 | apply H3 ]
      | apply H ].
Qed.

Lemma StepFun_P45 :
  forall (f:R -> R) (a b c:R),
    IsStepFun f a b -> a <= c <= b -> IsStepFun f c b.
Proof.
  intros f; intros; assert (H0 : a <= b).
  elim H; intros; apply Rle_trans with c; assumption.
  elim H; clear H; intros; unfold IsStepFun in X; unfold is_subdivision in X;
    elim X; clear X; intros l1 [lf1 H2];
      cut
        (forall (l1 lf1:Rlist) (a b c:R) (f:R -> R),
          adapted_couple f a b l1 lf1 ->
          a <= c <= b ->
          { l:Rlist & { l0:Rlist & adapted_couple f c b l l0 } }).
  intro X; unfold IsStepFun in |- *; unfold is_subdivision in |- *; eapply X;
    [ apply H2 | split; assumption ].
  clear f a b c H0 H H1 H2 l1 lf1; simple induction l1.
  intros; unfold adapted_couple in H; decompose [and] H; clear H; simpl in H4;
    discriminate.
  simple induction r0.
  intros X lf1 a b c f H H0; assert (H1 : a = b).
  unfold adapted_couple in H; decompose [and] H; clear H; simpl in H3;
    simpl in H2; assert (H7 : a <= b).
  elim H0; intros; apply Rle_trans with c; assumption.
  replace a with (Rmin a b).
  pattern b at 2 in |- *; replace b with (Rmax a b).
  rewrite <- H2; rewrite H3; reflexivity.
  unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; assumption ].
  unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; assumption ].
  split with (cons r nil); split with lf1; assert (H2 : c = b).
  rewrite H1 in H0; elim H0; intros; apply Rle_antisym; assumption.
  rewrite <- H2 in H1; rewrite <- H1; assumption.
  intros r1 r2 _ X0 lf1 a b c f H H0; induction  lf1 as [| r3 lf1 Hreclf1].
  unfold adapted_couple in H; decompose [and] H; clear H; simpl in H4;
    discriminate.
  clear Hreclf1; assert (H1 : {c <= r1} + {r1 < c}).
  case (Rle_dec c r1); intro; [ left; assumption | right; auto with real ].
  elim H1; intro.
  split with (cons c (cons r1 r2)); split with (cons r3 lf1);
    unfold adapted_couple in H; decompose [and] H; clear H;
      unfold adapted_couple in |- *; repeat split.
  unfold ordered_Rlist in |- *; intros; simpl in H; induction  i as [| i Hreci].
  simpl in |- *; assumption.
  clear Hreci; apply (H2 (S i)); simpl in |- *; assumption.
  simpl in |- *; unfold Rmin in |- *; case (Rle_dec c b); intro;
    [ reflexivity | elim n; elim H0; intros; assumption ].
  replace (Rmax c b) with (Rmax a b).
  rewrite <- H3; reflexivity.
  unfold Rmax in |- *; case (Rle_dec a b); case (Rle_dec c b); intros;
    [ reflexivity
      | elim n; elim H0; intros; assumption
      | elim n; elim H0; intros; apply Rle_trans with c; assumption
      | elim n0; elim H0; intros; apply Rle_trans with c; assumption ].
  simpl in |- *; simpl in H5; apply H5.
  intros; simpl in H; induction  i as [| i Hreci].
  unfold constant_D_eq, open_interval in |- *; intros; simpl in |- *;
    apply (H7 0%nat).
  simpl in |- *; apply lt_O_Sn.
  unfold open_interval in |- *; simpl in |- *; simpl in H6; elim H6; clear H6;
    intros; split; try assumption; apply Rle_lt_trans with c;
      try assumption; replace r with a.
  elim H0; intros; assumption.
  simpl in H4; rewrite H4; unfold Rmin in |- *; case (Rle_dec a b); intros;
    [ reflexivity
      | elim n; elim H0; intros; apply Rle_trans with c; assumption ].
  clear Hreci; apply (H7 (S i)); simpl in |- *; assumption.
  cut (adapted_couple f r1 b (cons r1 r2) lf1).
  cut (r1 <= c <= b).
  intros; elim (X0 _ _ _ _ _ H3 H2); intros l1' [lf1' H4]; split with l1';
    split with lf1'; assumption.
  split; [ left; assumption | elim H0; intros; assumption ].
  eapply StepFun_P7;
    [ elim H0; intros; apply Rle_trans with c; [ apply H2 | apply H3 ]
      | apply H ].
Qed.

Lemma StepFun_P46 :
  forall (f:R -> R) (a b c:R),
    IsStepFun f a b -> IsStepFun f b c -> IsStepFun f a c.
Proof.
  intros f; intros; case (Rle_dec a b); case (Rle_dec b c); intros.
  apply StepFun_P41 with b; assumption.
  case (Rle_dec a c); intro.
  apply StepFun_P44 with b; try assumption.
  split; [ assumption | auto with real ].
  apply StepFun_P6; apply StepFun_P44 with b.
  apply StepFun_P6; assumption.
  split; auto with real.
  case (Rle_dec a c); intro.
  apply StepFun_P45 with b; try assumption.
  split; auto with real.
  apply StepFun_P6; apply StepFun_P45 with b.
  apply StepFun_P6; assumption.
  split; [ assumption | auto with real ].
  apply StepFun_P6; apply StepFun_P41 with b;
    auto with real || apply StepFun_P6; assumption.
Qed.

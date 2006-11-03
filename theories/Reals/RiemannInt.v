(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Rfunctions.
Require Import SeqSeries.
Require Import Ranalysis.
Require Import Rbase.
Require Import RiemannInt_SF.
Require Import Classical_Prop.
Require Import Classical_Pred_Type.
Require Import Max. Open Local Scope R_scope.

Set Implicit Arguments.

(********************************************)
(**           Riemann's Integral            *)
(********************************************)

Definition Riemann_integrable (f:R -> R) (a b:R) : Type :=
  forall eps:posreal,
    sigT
    (fun phi:StepFun a b =>
      sigT
      (fun psi:StepFun a b =>
        (forall t:R,
          Rmin a b <= t <= Rmax a b -> Rabs (f t - phi t) <= psi t) /\
        Rabs (RiemannInt_SF psi) < eps)).

Definition phi_sequence (un:nat -> posreal) (f:R -> R) 
  (a b:R) (pr:Riemann_integrable f a b) (n:nat) := 
  projT1 (pr (un n)).

Lemma phi_sequence_prop :
  forall (un:nat -> posreal) (f:R -> R) (a b:R) (pr:Riemann_integrable f a b)
    (N:nat),
    sigT
    (fun psi:StepFun a b =>
      (forall t:R,
        Rmin a b <= t <= Rmax a b ->
        Rabs (f t - phi_sequence un pr N t) <= psi t) /\
      Rabs (RiemannInt_SF psi) < un N).
Proof.
  intros; apply (projT2 (pr (un N))).
Qed.

Lemma RiemannInt_P1 :
  forall (f:R -> R) (a b:R),
    Riemann_integrable f a b -> Riemann_integrable f b a.
Proof.
  unfold Riemann_integrable in |- *; intros; elim (X eps); clear X; intros;
    elim p; clear p; intros; apply existT with (mkStepFun (StepFun_P6 (pre x)));
      apply existT with (mkStepFun (StepFun_P6 (pre x0))); 
        elim p; clear p; intros; split.
  intros; apply (H t); elim H1; clear H1; intros; split;
    [ apply Rle_trans with (Rmin b a); try assumption; right;
      unfold Rmin in |- *
      | apply Rle_trans with (Rmax b a); try assumption; right;
        unfold Rmax in |- * ];
    (case (Rle_dec a b); case (Rle_dec b a); intros;
      try reflexivity || apply Rle_antisym;
        [ assumption | assumption | auto with real | auto with real ]).
  generalize H0; unfold RiemannInt_SF in |- *; case (Rle_dec a b);
    case (Rle_dec b a); intros;
      (replace
        (Int_SF (subdivision_val (mkStepFun (StepFun_P6 (pre x0))))
          (subdivision (mkStepFun (StepFun_P6 (pre x0))))) with
        (Int_SF (subdivision_val x0) (subdivision x0));
        [ idtac
          | apply StepFun_P17 with (fe x0) a b;
            [ apply StepFun_P1
              | apply StepFun_P2;
                apply (StepFun_P1 (mkStepFun (StepFun_P6 (pre x0)))) ] ]).
  apply H1.
  rewrite Rabs_Ropp; apply H1.
  rewrite Rabs_Ropp in H1; apply H1.
  apply H1.
Qed.

Lemma RiemannInt_P2 :
  forall (f:R -> R) (a b:R) (un:nat -> posreal) (vn wn:nat -> StepFun a b),
    Un_cv un 0 ->
    a <= b ->
    (forall n:nat,
      (forall t:R, Rmin a b <= t <= Rmax a b -> Rabs (f t - vn n t) <= wn n t) /\
      Rabs (RiemannInt_SF (wn n)) < un n) ->
    sigT (fun l:R => Un_cv (fun N:nat => RiemannInt_SF (vn N)) l).
Proof.
  intros; apply R_complete; unfold Un_cv in H; unfold Cauchy_crit in |- *;
    intros; assert (H3 : 0 < eps / 2).
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ assumption | apply Rinv_0_lt_compat; prove_sup0 ].
  elim (H _ H3); intros N0 H4; exists N0; intros; unfold R_dist in |- *;
    unfold R_dist in H4; elim (H1 n); elim (H1 m); intros;
      replace (RiemannInt_SF (vn n) - RiemannInt_SF (vn m)) with
      (RiemannInt_SF (vn n) + -1 * RiemannInt_SF (vn m)); 
      [ idtac | ring ]; rewrite <- StepFun_P30;
        apply Rle_lt_trans with
          (RiemannInt_SF
            (mkStepFun (StepFun_P32 (mkStepFun (StepFun_P28 (-1) (vn n) (vn m)))))).
  apply StepFun_P34; assumption.
  apply Rle_lt_trans with
    (RiemannInt_SF (mkStepFun (StepFun_P28 1 (wn n) (wn m)))).
  apply StepFun_P37; try assumption.
  intros; simpl in |- *;
    apply Rle_trans with (Rabs (vn n x - f x) + Rabs (f x - vn m x)).
  replace (vn n x + -1 * vn m x) with (vn n x - f x + (f x - vn m x));
  [ apply Rabs_triang | ring ].
  assert (H12 : Rmin a b = a).
  unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n0; assumption ].
  assert (H13 : Rmax a b = b).
  unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n0; assumption ].
  rewrite <- H12 in H11; pattern b at 2 in H11; rewrite <- H13 in H11;
    rewrite Rmult_1_l; apply Rplus_le_compat.
  rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr; apply H9.
  elim H11; intros; split; left; assumption.
  apply H7.
  elim H11; intros; split; left; assumption.
  rewrite StepFun_P30; rewrite Rmult_1_l; apply Rlt_trans with (un n + un m).
  apply Rle_lt_trans with
    (Rabs (RiemannInt_SF (wn n)) + Rabs (RiemannInt_SF (wn m))).
  apply Rplus_le_compat; apply RRle_abs.
  apply Rplus_lt_compat; assumption.
  apply Rle_lt_trans with (Rabs (un n) + Rabs (un m)).
  apply Rplus_le_compat; apply RRle_abs.
  replace (pos (un n)) with (un n - 0); [ idtac | ring ];
  replace (pos (un m)) with (un m - 0); [ idtac | ring ];
  rewrite (double_var eps); apply Rplus_lt_compat; apply H4; 
    assumption.
Qed.

Lemma RiemannInt_P3 :
  forall (f:R -> R) (a b:R) (un:nat -> posreal) (vn wn:nat -> StepFun a b),
    Un_cv un 0 ->
    (forall n:nat,
      (forall t:R, Rmin a b <= t <= Rmax a b -> Rabs (f t - vn n t) <= wn n t) /\
      Rabs (RiemannInt_SF (wn n)) < un n) ->
    sigT (fun l:R => Un_cv (fun N:nat => RiemannInt_SF (vn N)) l).
Proof.
  intros; case (Rle_dec a b); intro.
  apply RiemannInt_P2 with f un wn; assumption.
  assert (H1 : b <= a); auto with real.
  set (vn' := fun n:nat => mkStepFun (StepFun_P6 (pre (vn n))));
    set (wn' := fun n:nat => mkStepFun (StepFun_P6 (pre (wn n))));
      assert
        (H2 :
          forall n:nat,
            (forall t:R,
              Rmin b a <= t <= Rmax b a -> Rabs (f t - vn' n t) <= wn' n t) /\
            Rabs (RiemannInt_SF (wn' n)) < un n).
  intro; elim (H0 n0); intros; split.
  intros; apply (H2 t); elim H4; clear H4; intros; split;
    [ apply Rle_trans with (Rmin b a); try assumption; right;
      unfold Rmin in |- *
      | apply Rle_trans with (Rmax b a); try assumption; right;
        unfold Rmax in |- * ];
    (case (Rle_dec a b); case (Rle_dec b a); intros;
      try reflexivity || apply Rle_antisym;
        [ assumption | assumption | auto with real | auto with real ]).
  generalize H3; unfold RiemannInt_SF in |- *; case (Rle_dec a b);
    case (Rle_dec b a); unfold wn' in |- *; intros;
      (replace
        (Int_SF (subdivision_val (mkStepFun (StepFun_P6 (pre (wn n0)))))
          (subdivision (mkStepFun (StepFun_P6 (pre (wn n0)))))) with
        (Int_SF (subdivision_val (wn n0)) (subdivision (wn n0)));
        [ idtac
          | apply StepFun_P17 with (fe (wn n0)) a b;
            [ apply StepFun_P1
              | apply StepFun_P2;
                apply (StepFun_P1 (mkStepFun (StepFun_P6 (pre (wn n0))))) ] ]).
  apply H4.
  rewrite Rabs_Ropp; apply H4.
  rewrite Rabs_Ropp in H4; apply H4.
  apply H4.
  assert (H3 := RiemannInt_P2 _ _ _ _ H H1 H2); elim H3; intros;
    apply existT with (- x); unfold Un_cv in |- *; unfold Un_cv in p; 
      intros; elim (p _ H4); intros; exists x0; intros; 
        generalize (H5 _ H6); unfold R_dist, RiemannInt_SF in |- *;
          case (Rle_dec b a); case (Rle_dec a b); intros.
  elim n; assumption.
  unfold vn' in H7;
    replace (Int_SF (subdivision_val (vn n0)) (subdivision (vn n0))) with
    (Int_SF (subdivision_val (mkStepFun (StepFun_P6 (pre (vn n0)))))
      (subdivision (mkStepFun (StepFun_P6 (pre (vn n0))))));
    [ unfold Rminus in |- *; rewrite Ropp_involutive; rewrite <- Rabs_Ropp;
      rewrite Ropp_plus_distr; rewrite Ropp_involutive; 
        apply H7
      | symmetry  in |- *; apply StepFun_P17 with (fe (vn n0)) a b;
        [ apply StepFun_P1
          | apply StepFun_P2;
            apply (StepFun_P1 (mkStepFun (StepFun_P6 (pre (vn n0))))) ] ].
  elim n1; assumption.
  elim n2; assumption.
Qed.

Lemma RiemannInt_exists :
  forall (f:R -> R) (a b:R) (pr:Riemann_integrable f a b) 
    (un:nat -> posreal),
    Un_cv un 0 ->
    sigT
    (fun l:R => Un_cv (fun N:nat => RiemannInt_SF (phi_sequence un pr N)) l).
Proof.
  intros f; intros;
    apply RiemannInt_P3 with
      f un (fun n:nat => projT1 (phi_sequence_prop un pr n));
      [ apply H | intro; apply (projT2 (phi_sequence_prop un pr n)) ].
Qed.

Lemma RiemannInt_P4 :
  forall (f:R -> R) (a b l:R) (pr1 pr2:Riemann_integrable f a b)
    (un vn:nat -> posreal),
    Un_cv un 0 ->
    Un_cv vn 0 ->
    Un_cv (fun N:nat => RiemannInt_SF (phi_sequence un pr1 N)) l ->
    Un_cv (fun N:nat => RiemannInt_SF (phi_sequence vn pr2 N)) l.
Proof.
  unfold Un_cv in |- *; unfold R_dist in |- *; intros f; intros;
    assert (H3 : 0 < eps / 3).
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ assumption | apply Rinv_0_lt_compat; prove_sup0 ].
  elim (H _ H3); clear H; intros N0 H; elim (H0 _ H3); clear H0; intros N1 H0;
    elim (H1 _ H3); clear H1; intros N2 H1; set (N := max (max N0 N1) N2);
      exists N; intros;
        apply Rle_lt_trans with
          (Rabs
            (RiemannInt_SF (phi_sequence vn pr2 n) -
              RiemannInt_SF (phi_sequence un pr1 n)) +
            Rabs (RiemannInt_SF (phi_sequence un pr1 n) - l)).
  replace (RiemannInt_SF (phi_sequence vn pr2 n) - l) with
  (RiemannInt_SF (phi_sequence vn pr2 n) -
    RiemannInt_SF (phi_sequence un pr1 n) +
    (RiemannInt_SF (phi_sequence un pr1 n) - l)); [ apply Rabs_triang | ring ].
  replace eps with (2 * (eps / 3) + eps / 3).
  apply Rplus_lt_compat.
  elim (phi_sequence_prop vn pr2 n); intros psi_vn H5;
    elim (phi_sequence_prop un pr1 n); intros psi_un H6;
      replace
      (RiemannInt_SF (phi_sequence vn pr2 n) -
        RiemannInt_SF (phi_sequence un pr1 n)) with
      (RiemannInt_SF (phi_sequence vn pr2 n) +
        -1 * RiemannInt_SF (phi_sequence un pr1 n)); [ idtac | ring ];
      rewrite <- StepFun_P30.
  case (Rle_dec a b); intro.
  apply Rle_lt_trans with
    (RiemannInt_SF
      (mkStepFun
        (StepFun_P32
          (mkStepFun
            (StepFun_P28 (-1) (phi_sequence vn pr2 n)
              (phi_sequence un pr1 n)))))).
  apply StepFun_P34; assumption.
  apply Rle_lt_trans with
    (RiemannInt_SF (mkStepFun (StepFun_P28 1 psi_un psi_vn))).
  apply StepFun_P37; try assumption; intros; simpl in |- *; rewrite Rmult_1_l;
    apply Rle_trans with
      (Rabs (phi_sequence vn pr2 n x - f x) +
        Rabs (f x - phi_sequence un pr1 n x)).
  replace (phi_sequence vn pr2 n x + -1 * phi_sequence un pr1 n x) with
  (phi_sequence vn pr2 n x - f x + (f x - phi_sequence un pr1 n x));
  [ apply Rabs_triang | ring ].
  assert (H10 : Rmin a b = a).
  unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n0; assumption ].
  assert (H11 : Rmax a b = b).
  unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n0; assumption ].
  rewrite (Rplus_comm (psi_un x)); apply Rplus_le_compat.
  rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr; elim H5; intros; apply H8.
  rewrite H10; rewrite H11; elim H7; intros; split; left; assumption.
  elim H6; intros; apply H8.
  rewrite H10; rewrite H11; elim H7; intros; split; left; assumption.
  rewrite StepFun_P30; rewrite Rmult_1_l; rewrite double; apply Rplus_lt_compat.
  apply Rlt_trans with (pos (un n)).
  elim H6; intros; apply Rle_lt_trans with (Rabs (RiemannInt_SF psi_un)).
  apply RRle_abs.
  assumption.
  replace (pos (un n)) with (Rabs (un n - 0));
  [ apply H; unfold ge in |- *; apply le_trans with N; try assumption;
    unfold N in |- *; apply le_trans with (max N0 N1); 
      apply le_max_l
    | unfold Rminus in |- *; rewrite Ropp_0; rewrite Rplus_0_r; apply Rabs_right;
      apply Rle_ge; left; apply (cond_pos (un n)) ].
  apply Rlt_trans with (pos (vn n)).
  elim H5; intros; apply Rle_lt_trans with (Rabs (RiemannInt_SF psi_vn)).
  apply RRle_abs; assumption.
  assumption.
  replace (pos (vn n)) with (Rabs (vn n - 0));
  [ apply H0; unfold ge in |- *; apply le_trans with N; try assumption;
    unfold N in |- *; apply le_trans with (max N0 N1);
      [ apply le_max_r | apply le_max_l ]
    | unfold Rminus in |- *; rewrite Ropp_0; rewrite Rplus_0_r; apply Rabs_right;
      apply Rle_ge; left; apply (cond_pos (vn n)) ].
  rewrite StepFun_P39; rewrite Rabs_Ropp;
    apply Rle_lt_trans with
      (RiemannInt_SF
        (mkStepFun
          (StepFun_P32
            (mkStepFun
              (StepFun_P6
                (pre
                  (mkStepFun
                    (StepFun_P28 (-1) (phi_sequence vn pr2 n)
                      (phi_sequence un pr1 n))))))))).
  apply StepFun_P34; try auto with real.
  apply Rle_lt_trans with
    (RiemannInt_SF
      (mkStepFun (StepFun_P6 (pre (mkStepFun (StepFun_P28 1 psi_vn psi_un)))))).
  apply StepFun_P37.
  auto with real.
  intros; simpl in |- *; rewrite Rmult_1_l;
    apply Rle_trans with
      (Rabs (phi_sequence vn pr2 n x - f x) +
        Rabs (f x - phi_sequence un pr1 n x)).
  replace (phi_sequence vn pr2 n x + -1 * phi_sequence un pr1 n x) with
  (phi_sequence vn pr2 n x - f x + (f x - phi_sequence un pr1 n x));
  [ apply Rabs_triang | ring ].
  assert (H10 : Rmin a b = b).
  unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ elim n0; assumption | reflexivity ].
  assert (H11 : Rmax a b = a).
  unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ elim n0; assumption | reflexivity ].
  apply Rplus_le_compat.
  rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr; elim H5; intros; apply H8.
  rewrite H10; rewrite H11; elim H7; intros; split; left; assumption.
  elim H6; intros; apply H8.
  rewrite H10; rewrite H11; elim H7; intros; split; left; assumption.
  rewrite <-
    (Ropp_involutive
      (RiemannInt_SF
        (mkStepFun
          (StepFun_P6 (pre (mkStepFun (StepFun_P28 1 psi_vn psi_un)))))))
    ; rewrite <- StepFun_P39; rewrite StepFun_P30; rewrite Rmult_1_l;
      rewrite double; rewrite Ropp_plus_distr; apply Rplus_lt_compat.
  apply Rlt_trans with (pos (vn n)).
  elim H5; intros; apply Rle_lt_trans with (Rabs (RiemannInt_SF psi_vn)).
  rewrite <- Rabs_Ropp; apply RRle_abs.
  assumption.
  replace (pos (vn n)) with (Rabs (vn n - 0));
  [ apply H0; unfold ge in |- *; apply le_trans with N; try assumption;
    unfold N in |- *; apply le_trans with (max N0 N1);
      [ apply le_max_r | apply le_max_l ]
    | unfold R_dist in |- *; unfold Rminus in |- *; rewrite Ropp_0;
      rewrite Rplus_0_r; apply Rabs_right; apply Rle_ge; 
        left; apply (cond_pos (vn n)) ].
  apply Rlt_trans with (pos (un n)).
  elim H6; intros; apply Rle_lt_trans with (Rabs (RiemannInt_SF psi_un)).
  rewrite <- Rabs_Ropp; apply RRle_abs; assumption.
  assumption.
  replace (pos (un n)) with (Rabs (un n - 0));
  [ apply H; unfold ge in |- *; apply le_trans with N; try assumption;
    unfold N in |- *; apply le_trans with (max N0 N1); 
      apply le_max_l
    | unfold Rminus in |- *; rewrite Ropp_0; rewrite Rplus_0_r; apply Rabs_right;
      apply Rle_ge; left; apply (cond_pos (un n)) ].
  apply H1; unfold ge in |- *; apply le_trans with N; try assumption;
    unfold N in |- *; apply le_max_r.
  apply Rmult_eq_reg_l with 3;
    [ unfold Rdiv in |- *; rewrite Rmult_plus_distr_l;
      do 2 rewrite (Rmult_comm 3); repeat rewrite Rmult_assoc;
        rewrite <- Rinv_l_sym; [ ring | discrR ]
      | discrR ].
Qed.

Lemma RinvN_pos : forall n:nat, 0 < / (INR n + 1).
Proof.
  intro; apply Rinv_0_lt_compat; apply Rplus_le_lt_0_compat;
    [ apply pos_INR | apply Rlt_0_1 ].
Qed.

Definition RinvN (N:nat) : posreal := mkposreal _ (RinvN_pos N).

Lemma RinvN_cv : Un_cv RinvN 0.
Proof.
  unfold Un_cv in |- *; intros; assert (H0 := archimed (/ eps)); elim H0;
    clear H0; intros; assert (H2 : (0 <= up (/ eps))%Z).
  apply le_IZR; left; apply Rlt_trans with (/ eps);
    [ apply Rinv_0_lt_compat; assumption | assumption ].
  elim (IZN _ H2); intros; exists x; intros; unfold R_dist in |- *;
    simpl in |- *; unfold Rminus in |- *; rewrite Ropp_0; 
      rewrite Rplus_0_r; assert (H5 : 0 < INR n + 1).
  apply Rplus_le_lt_0_compat; [ apply pos_INR | apply Rlt_0_1 ].
  rewrite Rabs_right;
    [ idtac
      | left; change (0 < / (INR n + 1)) in |- *; apply Rinv_0_lt_compat;
        assumption ]; apply Rle_lt_trans with (/ (INR x + 1)).
  apply Rle_Rinv.
  apply Rplus_le_lt_0_compat; [ apply pos_INR | apply Rlt_0_1 ].
  assumption.
  do 2 rewrite <- (Rplus_comm 1); apply Rplus_le_compat_l; apply le_INR;
    apply H4.
  rewrite <- (Rinv_involutive eps).
  apply Rinv_lt_contravar.
  apply Rmult_lt_0_compat.
  apply Rinv_0_lt_compat; assumption.
  apply Rplus_le_lt_0_compat; [ apply pos_INR | apply Rlt_0_1 ].
  apply Rlt_trans with (INR x);
    [ rewrite INR_IZR_INZ; rewrite <- H3; apply H0
      | pattern (INR x) at 1 in |- *; rewrite <- Rplus_0_r;
        apply Rplus_lt_compat_l; apply Rlt_0_1 ].
  red in |- *; intro; rewrite H6 in H; elim (Rlt_irrefl _ H).
Qed.

(**********) 
Definition RiemannInt (f:R -> R) (a b:R) (pr:Riemann_integrable f a b) : R :=
  match RiemannInt_exists pr RinvN RinvN_cv with
    | existT a' b' => a'
  end.

Lemma RiemannInt_P5 :
  forall (f:R -> R) (a b:R) (pr1 pr2:Riemann_integrable f a b),
    RiemannInt pr1 = RiemannInt pr2.
Proof.
  intros; unfold RiemannInt in |- *;
    case (RiemannInt_exists pr1 RinvN RinvN_cv);
    case (RiemannInt_exists pr2 RinvN RinvN_cv); intros; 
      eapply UL_sequence;
        [ apply u0
          | apply RiemannInt_P4 with pr2 RinvN; apply RinvN_cv || assumption ].
Qed.

(***************************************)
(** C�([a,b]) is included in L1([a,b]) *)
(***************************************)

Lemma maxN :
  forall (a b:R) (del:posreal),
    a < b ->
    sigT (fun n:nat => a + INR n * del < b /\ b <= a + INR (S n) * del).
Proof.
  intros; set (I := fun n:nat => a + INR n * del < b);
    assert (H0 :  exists n : nat, I n).
  exists 0%nat; unfold I in |- *; rewrite Rmult_0_l; rewrite Rplus_0_r;
    assumption.
  cut (Nbound I).
  intro; assert (H2 := Nzorn H0 H1); elim H2; intros; exists x; elim p; intros;
    split.
  apply H3.
  case (total_order_T (a + INR (S x) * del) b); intro.
  elim s; intro.
  assert (H5 := H4 (S x) a0); elim (le_Sn_n _ H5).
  right; symmetry  in |- *; assumption.
  left; apply r.
  assert (H1 : 0 <= (b - a) / del).
  unfold Rdiv in |- *; apply Rmult_le_pos;
    [ apply Rge_le; apply Rge_minus; apply Rle_ge; left; apply H
      | left; apply Rinv_0_lt_compat; apply (cond_pos del) ].
  elim (archimed ((b - a) / del)); intros;
    assert (H4 : (0 <= up ((b - a) / del))%Z).
  apply le_IZR; simpl in |- *; left; apply Rle_lt_trans with ((b - a) / del);
    assumption.
  assert (H5 := IZN _ H4); elim H5; clear H5; intros N H5;
    unfold Nbound in |- *; exists N; intros; unfold I in H6; 
      apply INR_le; rewrite H5 in H2; rewrite <- INR_IZR_INZ in H2; 
        left; apply Rle_lt_trans with ((b - a) / del); try assumption;
          apply Rmult_le_reg_l with (pos del);
            [ apply (cond_pos del)
              | unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ del));
                rewrite <- Rmult_assoc; rewrite <- Rinv_r_sym;
                  [ rewrite Rmult_1_l; rewrite Rmult_comm; apply Rplus_le_reg_l with a;
                    replace (a + (b - a)) with b; [ left; assumption | ring ]
                    | assert (H7 := cond_pos del); red in |- *; intro; rewrite H8 in H7;
                      elim (Rlt_irrefl _ H7) ] ].
Qed.

Fixpoint SubEquiN (N:nat) (x y:R) (del:posreal) {struct N} : Rlist :=
  match N with
    | O => cons y nil
    | S p => cons x (SubEquiN p (x + del) y del)
  end.

Definition max_N (a b:R) (del:posreal) (h:a < b) : nat :=
  match maxN del h with
    | existT N H0 => N
  end.

Definition SubEqui (a b:R) (del:posreal) (h:a < b) : Rlist :=
  SubEquiN (S (max_N del h)) a b del.

Lemma Heine_cor1 :
  forall (f:R -> R) (a b:R),
    a < b ->
    (forall x:R, a <= x <= b -> continuity_pt f x) ->
    forall eps:posreal,
      sigT
      (fun delta:posreal =>
        delta <= b - a /\
        (forall x y:R,
          a <= x <= b ->
          a <= y <= b -> Rabs (x - y) < delta -> Rabs (f x - f y) < eps)).
Proof.
  intro f; intros;
    set
      (E :=
        fun l:R =>
          0 < l <= b - a /\
          (forall x y:R,
            a <= x <= b ->
            a <= y <= b -> Rabs (x - y) < l -> Rabs (f x - f y) < eps));
      assert (H1 : bound E).
  unfold bound in |- *; exists (b - a); unfold is_upper_bound in |- *; intros;
    unfold E in H1; elim H1; clear H1; intros H1 _; elim H1; 
      intros; assumption.
  assert (H2 :  exists x : R, E x).
  assert (H2 := Heine f (fun x:R => a <= x <= b) (compact_P3 a b) H0 eps);
    elim H2; intros; exists (Rmin x (b - a)); unfold E in |- *; 
      split;
        [ split;
          [ unfold Rmin in |- *; case (Rle_dec x (b - a)); intro;
            [ apply (cond_pos x) | apply Rlt_Rminus; assumption ]
            | apply Rmin_r ]
          | intros; apply H3; try assumption; apply Rlt_le_trans with (Rmin x (b - a));
            [ assumption | apply Rmin_l ] ].
  assert (H3 := completeness E H1 H2); elim H3; intros; cut (0 < x <= b - a).
  intro; elim H4; clear H4; intros; apply existT with (mkposreal _ H4); split.
  apply H5.
  unfold is_lub in p; elim p; intros; unfold is_upper_bound in H6;
    set (D := Rabs (x0 - y)); elim (classic (exists y : R, D < y /\ E y));
      intro.
  elim H11; intros; elim H12; clear H12; intros; unfold E in H13; elim H13;
    intros; apply H15; assumption.
  assert (H12 := not_ex_all_not _ (fun y:R => D < y /\ E y) H11);
    assert (H13 : is_upper_bound E D).
  unfold is_upper_bound in |- *; intros; assert (H14 := H12 x1);
    elim (not_and_or (D < x1) (E x1) H14); intro.
  case (Rle_dec x1 D); intro.
  assumption.
  elim H15; auto with real.
  elim H15; assumption.
  assert (H14 := H7 _ H13); elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H14 H10)).
  unfold is_lub in p; unfold is_upper_bound in p; elim p; clear p; intros;
    split.
  elim H2; intros; assert (H7 := H4 _ H6); unfold E in H6; elim H6; clear H6;
    intros H6 _; elim H6; intros; apply Rlt_le_trans with x0; 
      assumption.
  apply H5; intros; unfold E in H6; elim H6; clear H6; intros H6 _; elim H6;
    intros; assumption.
Qed.

Lemma Heine_cor2 :
  forall (f:R -> R) (a b:R),
    (forall x:R, a <= x <= b -> continuity_pt f x) ->
    forall eps:posreal,
      sigT
      (fun delta:posreal =>
        forall x y:R,
          a <= x <= b ->
          a <= y <= b -> Rabs (x - y) < delta -> Rabs (f x - f y) < eps).
Proof.
  intro f; intros; case (total_order_T a b); intro.
  elim s; intro.
  assert (H0 := Heine_cor1 a0 H eps); elim H0; intros; apply existT with x;
    elim p; intros; apply H2; assumption.
  apply existT with (mkposreal _ Rlt_0_1); intros; assert (H3 : x = y);
    [ elim H0; elim H1; intros; rewrite b0 in H3; rewrite b0 in H5;
      apply Rle_antisym; apply Rle_trans with b; assumption
      | rewrite H3; unfold Rminus in |- *; rewrite Rplus_opp_r; rewrite Rabs_R0;
        apply (cond_pos eps) ].
  apply existT with (mkposreal _ Rlt_0_1); intros; elim H0; intros;
    elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ (Rle_trans _ _ _ H3 H4) r)).
Qed.

Lemma SubEqui_P1 :
  forall (a b:R) (del:posreal) (h:a < b), pos_Rl (SubEqui del h) 0 = a.
Proof.
  intros; unfold SubEqui in |- *; case (maxN del h); intros; reflexivity.
Qed.

Lemma SubEqui_P2 :
  forall (a b:R) (del:posreal) (h:a < b),
    pos_Rl (SubEqui del h) (pred (Rlength (SubEqui del h))) = b.
Proof.
  intros; unfold SubEqui in |- *; case (maxN del h); intros; clear a0;
    cut
      (forall (x:nat) (a:R) (del:posreal),
        pos_Rl (SubEquiN (S x) a b del)
        (pred (Rlength (SubEquiN (S x) a b del))) = b);
      [ intro; apply H
        | simple induction x0;
          [ intros; reflexivity
            | intros;
              change
                (pos_Rl (SubEquiN (S n) (a0 + del0) b del0)
                  (pred (Rlength (SubEquiN (S n) (a0 + del0) b del0))) = b) 
                in |- *; apply H ] ].
Qed.

Lemma SubEqui_P3 :
  forall (N:nat) (a b:R) (del:posreal), Rlength (SubEquiN N a b del) = S N.
Proof.
  simple induction N; intros;
    [ reflexivity | simpl in |- *; rewrite H; reflexivity ].
Qed.

Lemma SubEqui_P4 :
  forall (N:nat) (a b:R) (del:posreal) (i:nat),
    (i < S N)%nat -> pos_Rl (SubEquiN (S N) a b del) i = a + INR i * del.
Proof.
  simple induction N;
    [ intros; inversion H; [ simpl in |- *; ring | elim (le_Sn_O _ H1) ]
      | intros; induction  i as [| i Hreci];
        [ simpl in |- *; ring
          | change
            (pos_Rl (SubEquiN (S n) (a + del) b del) i = a + INR (S i) * del)
            in |- *; rewrite H; [ rewrite S_INR; ring | apply lt_S_n; apply H0 ] ] ].
Qed.

Lemma SubEqui_P5 :
  forall (a b:R) (del:posreal) (h:a < b),
    Rlength (SubEqui del h) = S (S (max_N del h)).
Proof.
  intros; unfold SubEqui in |- *; apply SubEqui_P3.
Qed.

Lemma SubEqui_P6 :
  forall (a b:R) (del:posreal) (h:a < b) (i:nat),
    (i < S (max_N del h))%nat -> pos_Rl (SubEqui del h) i = a + INR i * del.
Proof.
  intros; unfold SubEqui in |- *; apply SubEqui_P4; assumption.
Qed.

Lemma SubEqui_P7 :
  forall (a b:R) (del:posreal) (h:a < b), ordered_Rlist (SubEqui del h).
Proof.
  intros; unfold ordered_Rlist in |- *; intros; rewrite SubEqui_P5 in H;
    simpl in H; inversion H.
  rewrite (SubEqui_P6 del h (i:=(max_N del h))).
  replace (S (max_N del h)) with (pred (Rlength (SubEqui del h))).
  rewrite SubEqui_P2; unfold max_N in |- *; case (maxN del h); intros; left;
    elim a0; intros; assumption.
  rewrite SubEqui_P5; reflexivity.
  apply lt_n_Sn.
  repeat rewrite SubEqui_P6.
  3: assumption.
  2: apply le_lt_n_Sm; assumption.
  apply Rplus_le_compat_l; rewrite S_INR; rewrite Rmult_plus_distr_r;
    pattern (INR i * del) at 1 in |- *; rewrite <- Rplus_0_r;
      apply Rplus_le_compat_l; rewrite Rmult_1_l; left; 
        apply (cond_pos del).
Qed.

Lemma SubEqui_P8 :
  forall (a b:R) (del:posreal) (h:a < b) (i:nat),
    (i < Rlength (SubEqui del h))%nat -> a <= pos_Rl (SubEqui del h) i <= b.
Proof.
  intros; split.
  pattern a at 1 in |- *; rewrite <- (SubEqui_P1 del h); apply RList_P5.
  apply SubEqui_P7.
  elim (RList_P3 (SubEqui del h) (pos_Rl (SubEqui del h) i)); intros; apply H1;
    exists i; split; [ reflexivity | assumption ].
  pattern b at 2 in |- *; rewrite <- (SubEqui_P2 del h); apply RList_P7;
    [ apply SubEqui_P7
      | elim (RList_P3 (SubEqui del h) (pos_Rl (SubEqui del h) i)); intros;
        apply H1; exists i; split; [ reflexivity | assumption ] ].
Qed.

Lemma SubEqui_P9 :
  forall (a b:R) (del:posreal) (f:R -> R) (h:a < b),
    sigT
    (fun g:StepFun a b =>
      g b = f b /\
      (forall i:nat,
        (i < pred (Rlength (SubEqui del h)))%nat ->
        constant_D_eq g
        (co_interval (pos_Rl (SubEqui del h) i)
          (pos_Rl (SubEqui del h) (S i)))
        (f (pos_Rl (SubEqui del h) i)))).
Proof.
  intros; apply StepFun_P38;
    [ apply SubEqui_P7 | apply SubEqui_P1 | apply SubEqui_P2 ].
Qed.

Lemma RiemannInt_P6 :
  forall (f:R -> R) (a b:R),
    a < b ->
    (forall x:R, a <= x <= b -> continuity_pt f x) -> Riemann_integrable f a b.
Proof.
  intros; unfold Riemann_integrable in |- *; intro;
    assert (H1 : 0 < eps / (2 * (b - a))).
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ apply (cond_pos eps)
      | apply Rinv_0_lt_compat; apply Rmult_lt_0_compat;
        [ prove_sup0 | apply Rlt_Rminus; assumption ] ].
  assert (H2 : Rmin a b = a).
  unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; left; assumption ].
  assert (H3 : Rmax a b = b).
  unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; left; assumption ].
  elim (Heine_cor2 H0 (mkposreal _ H1)); intros del H4;
    elim (SubEqui_P9 del f H); intros phi [H5 H6]; split with phi;
      split with (mkStepFun (StepFun_P4 a b (eps / (2 * (b - a))))); 
        split.
  2: rewrite StepFun_P18; unfold Rdiv in |- *; rewrite Rinv_mult_distr.
  2: do 2 rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
  2: rewrite Rmult_1_r; rewrite Rabs_right.
  2: apply Rmult_lt_reg_l with 2.
  2: prove_sup0.
  2: rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
    rewrite <- Rinv_r_sym.
  2: rewrite Rmult_1_l; pattern (pos eps) at 1 in |- *; rewrite <- Rplus_0_r;
    rewrite double; apply Rplus_lt_compat_l; apply (cond_pos eps).
  2: discrR.
  2: apply Rle_ge; left; apply Rmult_lt_0_compat.
  2: apply (cond_pos eps).
  2: apply Rinv_0_lt_compat; prove_sup0.
  2: apply Rminus_eq_contra; red in |- *; intro; clear H6; rewrite H7 in H;
    elim (Rlt_irrefl _ H).
  2: discrR.
  2: apply Rminus_eq_contra; red in |- *; intro; clear H6; rewrite H7 in H;
    elim (Rlt_irrefl _ H).
  intros; rewrite H2 in H7; rewrite H3 in H7; simpl in |- *;
    unfold fct_cte in |- *;
      cut
        (forall t:R,
          a <= t <= b ->
          t = b \/
          (exists i : nat,
            (i < pred (Rlength (SubEqui del H)))%nat /\
            co_interval (pos_Rl (SubEqui del H) i) (pos_Rl (SubEqui del H) (S i))
            t)).
  intro; elim (H8 _ H7); intro.
  rewrite H9; rewrite H5; unfold Rminus in |- *; rewrite Rplus_opp_r;
    rewrite Rabs_R0; left; assumption.
  elim H9; clear H9; intros I [H9 H10]; assert (H11 := H6 I H9 t H10);
    rewrite H11; left; apply H4.
  assumption.
  apply SubEqui_P8; apply lt_trans with (pred (Rlength (SubEqui del H))).
  assumption.
  apply lt_pred_n_n; apply neq_O_lt; red in |- *; intro; rewrite <- H12 in H9;
    elim (lt_n_O _ H9).
  unfold co_interval in H10; elim H10; clear H10; intros; rewrite Rabs_right.
  rewrite SubEqui_P5 in H9; simpl in H9; inversion H9.
  apply Rplus_lt_reg_r with (pos_Rl (SubEqui del H) (max_N del H)).
  replace
  (pos_Rl (SubEqui del H) (max_N del H) +
    (t - pos_Rl (SubEqui del H) (max_N del H))) with t; 
  [ idtac | ring ]; apply Rlt_le_trans with b.
  rewrite H14 in H12;
    assert (H13 : S (max_N del H) = pred (Rlength (SubEqui del H))).
  rewrite SubEqui_P5; reflexivity.
  rewrite H13 in H12; rewrite SubEqui_P2 in H12; apply H12.
  rewrite SubEqui_P6.
  2: apply lt_n_Sn.
  unfold max_N in |- *; case (maxN del H); intros; elim a0; clear a0;
    intros _ H13; replace (a + INR x * del + del) with (a + INR (S x) * del);
      [ assumption | rewrite S_INR; ring ].
  apply Rplus_lt_reg_r with (pos_Rl (SubEqui del H) I);
    replace (pos_Rl (SubEqui del H) I + (t - pos_Rl (SubEqui del H) I)) with t;
    [ idtac | ring ];
    replace (pos_Rl (SubEqui del H) I + del) with (pos_Rl (SubEqui del H) (S I)).
  assumption.
  repeat rewrite SubEqui_P6.
  rewrite S_INR; ring.
  assumption.
  apply le_lt_n_Sm; assumption.
  apply Rge_minus; apply Rle_ge; assumption.
  intros; clear H0 H1 H4 phi H5 H6 t H7; case (Req_dec t0 b); intro.
  left; assumption.
  right; set (I := fun j:nat => a + INR j * del <= t0);
    assert (H1 :  exists n : nat, I n).
  exists 0%nat; unfold I in |- *; rewrite Rmult_0_l; rewrite Rplus_0_r; elim H8;
    intros; assumption.
  assert (H4 : Nbound I).
  unfold Nbound in |- *; exists (S (max_N del H)); intros; unfold max_N in |- *;
    case (maxN del H); intros; elim a0; clear a0; intros _ H5; 
      apply INR_le; apply Rmult_le_reg_l with (pos del).
  apply (cond_pos del).
  apply Rplus_le_reg_l with a; do 2 rewrite (Rmult_comm del);
    apply Rle_trans with t0; unfold I in H4; try assumption;
      apply Rle_trans with b; try assumption; elim H8; intros; 
        assumption.
  elim (Nzorn H1 H4); intros N [H5 H6]; assert (H7 : (N < S (max_N del H))%nat).
  unfold max_N in |- *; case (maxN del H); intros; apply INR_lt;
    apply Rmult_lt_reg_l with (pos del).
  apply (cond_pos del).
  apply Rplus_lt_reg_r with a; do 2 rewrite (Rmult_comm del);
    apply Rle_lt_trans with t0; unfold I in H5; try assumption; 
      elim a0; intros; apply Rlt_le_trans with b; try assumption; 
        elim H8; intros.
  elim H11; intro.
  assumption.
  elim H0; assumption.
  exists N; split.
  rewrite SubEqui_P5; simpl in |- *; assumption.
  unfold co_interval in |- *; split.
  rewrite SubEqui_P6.
  apply H5.
  assumption.
  inversion H7.
  replace (S (max_N del H)) with (pred (Rlength (SubEqui del H))).
  rewrite (SubEqui_P2 del H); elim H8; intros.
  elim H11; intro.
  assumption.
  elim H0; assumption.
  rewrite SubEqui_P5; reflexivity.
  rewrite SubEqui_P6.
  case (Rle_dec (a + INR (S N) * del) t0); intro.
  assert (H11 := H6 (S N) r); elim (le_Sn_n _ H11).
  auto with real.
  apply le_lt_n_Sm; assumption.
Qed.

Lemma RiemannInt_P7 : forall (f:R -> R) (a:R), Riemann_integrable f a a.
Proof.
  unfold Riemann_integrable in |- *; intro f; intros;
    split with (mkStepFun (StepFun_P4 a a (f a)));
      split with (mkStepFun (StepFun_P4 a a 0)); split.
  intros; simpl in |- *; unfold fct_cte in |- *; replace t with a.
  unfold Rminus in |- *; rewrite Rplus_opp_r; rewrite Rabs_R0; right;
    reflexivity.
  generalize H; unfold Rmin, Rmax in |- *; case (Rle_dec a a); intros; elim H0;
    intros; apply Rle_antisym; assumption.
  rewrite StepFun_P18; rewrite Rmult_0_l; rewrite Rabs_R0; apply (cond_pos eps).
Qed.

Lemma continuity_implies_RiemannInt :
  forall (f:R -> R) (a b:R),
    a <= b ->
    (forall x:R, a <= x <= b -> continuity_pt f x) -> Riemann_integrable f a b.
Proof.
  intros; case (total_order_T a b); intro;
    [ elim s; intro;
      [ apply RiemannInt_P6; assumption | rewrite b0; apply RiemannInt_P7 ]
      | elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H r)) ].
Qed.

Lemma RiemannInt_P8 :
  forall (f:R -> R) (a b:R) (pr1:Riemann_integrable f a b)
    (pr2:Riemann_integrable f b a), RiemannInt pr1 = - RiemannInt pr2.
Proof.
  intro f; intros; eapply UL_sequence.
  unfold RiemannInt in |- *; case (RiemannInt_exists pr1 RinvN RinvN_cv);
    intros; apply u.
  unfold RiemannInt in |- *; case (RiemannInt_exists pr2 RinvN RinvN_cv);
    intros;
      cut
        (exists psi1 : nat -> StepFun a b,
          (forall n:nat,
            (forall t:R,
              Rmin a b <= t /\ t <= Rmax a b ->
              Rabs (f t - phi_sequence RinvN pr1 n t) <= psi1 n t) /\
            Rabs (RiemannInt_SF (psi1 n)) < RinvN n)).
  cut
    (exists psi2 : nat -> StepFun b a,
      (forall n:nat,
        (forall t:R,
          Rmin a b <= t /\ t <= Rmax a b ->
          Rabs (f t - phi_sequence RinvN pr2 n t) <= psi2 n t) /\
        Rabs (RiemannInt_SF (psi2 n)) < RinvN n)).
  intros; elim H; clear H; intros psi2 H; elim H0; clear H0; intros psi1 H0;
    assert (H1 := RinvN_cv); unfold Un_cv in |- *; intros;
      assert (H3 : 0 < eps / 3).
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ assumption | apply Rinv_0_lt_compat; prove_sup0 ].
  unfold Un_cv in H1; elim (H1 _ H3); clear H1; intros N0 H1;
    unfold R_dist in H1; simpl in H1;
      assert (H4 : forall n:nat, (n >= N0)%nat -> RinvN n < eps / 3).
  intros; assert (H5 := H1 _ H4);
    replace (pos (RinvN n)) with (Rabs (/ (INR n + 1) - 0));
    [ assumption
      | unfold Rminus in |- *; rewrite Ropp_0; rewrite Rplus_0_r; apply Rabs_right;
        left; apply (cond_pos (RinvN n)) ].
  clear H1; unfold Un_cv in u; elim (u _ H3); clear u; intros N1 H1;
    exists (max N0 N1); intros; unfold R_dist in |- *;
      apply Rle_lt_trans with
        (Rabs
          (RiemannInt_SF (phi_sequence RinvN pr1 n) +
            RiemannInt_SF (phi_sequence RinvN pr2 n)) +
          Rabs (RiemannInt_SF (phi_sequence RinvN pr2 n) - x)).
  rewrite <- (Rabs_Ropp (RiemannInt_SF (phi_sequence RinvN pr2 n) - x));
    replace (RiemannInt_SF (phi_sequence RinvN pr1 n) - - x) with
    (RiemannInt_SF (phi_sequence RinvN pr1 n) +
      RiemannInt_SF (phi_sequence RinvN pr2 n) +
      - (RiemannInt_SF (phi_sequence RinvN pr2 n) - x));
    [ apply Rabs_triang | ring ].
  replace eps with (2 * (eps / 3) + eps / 3).
  apply Rplus_lt_compat.
  rewrite (StepFun_P39 (phi_sequence RinvN pr2 n));
    replace
    (RiemannInt_SF (phi_sequence RinvN pr1 n) +
      - RiemannInt_SF (mkStepFun (StepFun_P6 (pre (phi_sequence RinvN pr2 n)))))
    with
      (RiemannInt_SF (phi_sequence RinvN pr1 n) +
        -1 *
        RiemannInt_SF (mkStepFun (StepFun_P6 (pre (phi_sequence RinvN pr2 n)))));
      [ idtac | ring ]; rewrite <- StepFun_P30.
  case (Rle_dec a b); intro.
  apply Rle_lt_trans with
    (RiemannInt_SF
      (mkStepFun
        (StepFun_P32
          (mkStepFun
            (StepFun_P28 (-1) (phi_sequence RinvN pr1 n)
              (mkStepFun (StepFun_P6 (pre (phi_sequence RinvN pr2 n))))))))).
  apply StepFun_P34; assumption.
  apply Rle_lt_trans with
    (RiemannInt_SF
      (mkStepFun
        (StepFun_P28 1 (psi1 n) (mkStepFun (StepFun_P6 (pre (psi2 n))))))).
  apply StepFun_P37; try assumption.
  intros; simpl in |- *; rewrite Rmult_1_l;
    apply Rle_trans with
      (Rabs (phi_sequence RinvN pr1 n x0 - f x0) +
        Rabs (f x0 - phi_sequence RinvN pr2 n x0)).
  replace (phi_sequence RinvN pr1 n x0 + -1 * phi_sequence RinvN pr2 n x0) with
  (phi_sequence RinvN pr1 n x0 - f x0 + (f x0 - phi_sequence RinvN pr2 n x0));
  [ apply Rabs_triang | ring ].
  assert (H7 : Rmin a b = a).
  unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n0; assumption ].
  assert (H8 : Rmax a b = b).
  unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n0; assumption ].
  apply Rplus_le_compat.
  elim (H0 n); intros; rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr; apply H9;
    rewrite H7; rewrite H8.
  elim H6; intros; split; left; assumption.
  elim (H n); intros; apply H9; rewrite H7; rewrite H8.
  elim H6; intros; split; left; assumption.
  rewrite StepFun_P30; rewrite Rmult_1_l; rewrite double; apply Rplus_lt_compat.
  elim (H0 n); intros; apply Rle_lt_trans with (Rabs (RiemannInt_SF (psi1 n)));
    [ apply RRle_abs
      | apply Rlt_trans with (pos (RinvN n));
        [ assumption
          | apply H4; unfold ge in |- *; apply le_trans with (max N0 N1);
            [ apply le_max_l | assumption ] ] ].
  elim (H n); intros;
    rewrite <-
      (Ropp_involutive (RiemannInt_SF (mkStepFun (StepFun_P6 (pre (psi2 n))))))
      ; rewrite <- StepFun_P39;
        apply Rle_lt_trans with (Rabs (RiemannInt_SF (psi2 n)));
          [ rewrite <- Rabs_Ropp; apply RRle_abs
            | apply Rlt_trans with (pos (RinvN n));
              [ assumption
                | apply H4; unfold ge in |- *; apply le_trans with (max N0 N1);
                  [ apply le_max_l | assumption ] ] ].
  assert (Hyp : b <= a).
  auto with real.
  rewrite StepFun_P39; rewrite Rabs_Ropp;
    apply Rle_lt_trans with
      (RiemannInt_SF
        (mkStepFun
          (StepFun_P32
            (mkStepFun
              (StepFun_P6
                (StepFun_P28 (-1) (phi_sequence RinvN pr1 n)
                  (mkStepFun (StepFun_P6 (pre (phi_sequence RinvN pr2 n)))))))))).
  apply StepFun_P34; assumption.
  apply Rle_lt_trans with
    (RiemannInt_SF
      (mkStepFun
        (StepFun_P28 1 (mkStepFun (StepFun_P6 (pre (psi1 n)))) (psi2 n)))).
  apply StepFun_P37; try assumption.
  intros; simpl in |- *; rewrite Rmult_1_l;
    apply Rle_trans with
      (Rabs (phi_sequence RinvN pr1 n x0 - f x0) +
        Rabs (f x0 - phi_sequence RinvN pr2 n x0)).
  replace (phi_sequence RinvN pr1 n x0 + -1 * phi_sequence RinvN pr2 n x0) with
  (phi_sequence RinvN pr1 n x0 - f x0 + (f x0 - phi_sequence RinvN pr2 n x0));
  [ apply Rabs_triang | ring ].
  assert (H7 : Rmin a b = b).
  unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ elim n0; assumption | reflexivity ].
  assert (H8 : Rmax a b = a).
  unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ elim n0; assumption | reflexivity ].
  apply Rplus_le_compat.
  elim (H0 n); intros; rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr; apply H9;
    rewrite H7; rewrite H8.
  elim H6; intros; split; left; assumption.
  elim (H n); intros; apply H9; rewrite H7; rewrite H8; elim H6; intros; split;
    left; assumption.
  rewrite StepFun_P30; rewrite Rmult_1_l; rewrite double; apply Rplus_lt_compat.
  elim (H0 n); intros;
    rewrite <-
      (Ropp_involutive (RiemannInt_SF (mkStepFun (StepFun_P6 (pre (psi1 n))))))
      ; rewrite <- StepFun_P39;
        apply Rle_lt_trans with (Rabs (RiemannInt_SF (psi1 n)));
          [ rewrite <- Rabs_Ropp; apply RRle_abs
            | apply Rlt_trans with (pos (RinvN n));
              [ assumption
                | apply H4; unfold ge in |- *; apply le_trans with (max N0 N1);
                  [ apply le_max_l | assumption ] ] ].
  elim (H n); intros; apply Rle_lt_trans with (Rabs (RiemannInt_SF (psi2 n)));
    [ apply RRle_abs
      | apply Rlt_trans with (pos (RinvN n));
        [ assumption
          | apply H4; unfold ge in |- *; apply le_trans with (max N0 N1);
            [ apply le_max_l | assumption ] ] ].
  unfold R_dist in H1; apply H1; unfold ge in |- *;
    apply le_trans with (max N0 N1); [ apply le_max_r | assumption ].
  apply Rmult_eq_reg_l with 3;
    [ unfold Rdiv in |- *; rewrite Rmult_plus_distr_l;
      do 2 rewrite (Rmult_comm 3); repeat rewrite Rmult_assoc;
        rewrite <- Rinv_l_sym; [ ring | discrR ]
      | discrR ].
  split with (fun n:nat => projT1 (phi_sequence_prop RinvN pr2 n)); intro;
    rewrite Rmin_comm; rewrite RmaxSym;
      apply (projT2 (phi_sequence_prop RinvN pr2 n)).
  split with (fun n:nat => projT1 (phi_sequence_prop RinvN pr1 n)); intro;
    apply (projT2 (phi_sequence_prop RinvN pr1 n)).
Qed.

Lemma RiemannInt_P9 :
  forall (f:R -> R) (a:R) (pr:Riemann_integrable f a a), RiemannInt pr = 0.
Proof.
  intros; assert (H := RiemannInt_P8 pr pr); apply Rmult_eq_reg_l with 2;
    [ rewrite Rmult_0_r; rewrite double; pattern (RiemannInt pr) at 2 in |- *;
      rewrite H; apply Rplus_opp_r
      | discrR ].
Qed.

Lemma Req_EM_T : forall r1 r2:R, {r1 = r2} + {r1 <> r2}.
Proof.
  intros; elim (total_order_T r1 r2); intros;
    [ elim a; intro;
      [ right; red in |- *; intro; rewrite H in a0; elim (Rlt_irrefl r2 a0)
        | left; assumption ]
      | right; red in |- *; intro; rewrite H in b; elim (Rlt_irrefl r2 b) ].
Qed.

(* L1([a,b]) is a vectorial space *)
Lemma RiemannInt_P10 :
  forall (f g:R -> R) (a b l:R),
    Riemann_integrable f a b ->
    Riemann_integrable g a b ->
    Riemann_integrable (fun x:R => f x + l * g x) a b.
Proof.
  unfold Riemann_integrable in |- *; intros f g; intros; case (Req_EM_T l 0);
    intro.
  elim (X eps); intros; split with x; elim p; intros; split with x0; elim p0;
    intros; split; try assumption; rewrite e; intros; 
      rewrite Rmult_0_l; rewrite Rplus_0_r; apply H; assumption.
  assert (H : 0 < eps / 2).
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ apply (cond_pos eps) | apply Rinv_0_lt_compat; prove_sup0 ].
  assert (H0 : 0 < eps / (2 * Rabs l)).
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ apply (cond_pos eps)
      | apply Rinv_0_lt_compat; apply Rmult_lt_0_compat;
        [ prove_sup0 | apply Rabs_pos_lt; assumption ] ].
  elim (X (mkposreal _ H)); intros; elim (X0 (mkposreal _ H0)); intros;
    split with (mkStepFun (StepFun_P28 l x x0)); elim p0; 
      elim p; intros; split with (mkStepFun (StepFun_P28 (Rabs l) x1 x2)); 
        elim p1; elim p2; clear p1 p2 p0 p X X0; intros; split.
  intros; simpl in |- *;
    apply Rle_trans with (Rabs (f t - x t) + Rabs (l * (g t - x0 t))).
  replace (f t + l * g t - (x t + l * x0 t)) with
  (f t - x t + l * (g t - x0 t)); [ apply Rabs_triang | ring ].
  apply Rplus_le_compat;
    [ apply H3; assumption
      | rewrite Rabs_mult; apply Rmult_le_compat_l;
        [ apply Rabs_pos | apply H1; assumption ] ].
  rewrite StepFun_P30;
    apply Rle_lt_trans with
      (Rabs (RiemannInt_SF x1) + Rabs (Rabs l * RiemannInt_SF x2)).
  apply Rabs_triang.
  rewrite (double_var eps); apply Rplus_lt_compat.
  apply H4.
  rewrite Rabs_mult; rewrite Rabs_Rabsolu; apply Rmult_lt_reg_l with (/ Rabs l).
  apply Rinv_0_lt_compat; apply Rabs_pos_lt; assumption.
  rewrite <- Rmult_assoc; rewrite <- Rinv_l_sym;
    [ rewrite Rmult_1_l;
      replace (/ Rabs l * (eps / 2)) with (eps / (2 * Rabs l));
      [ apply H2
        | unfold Rdiv in |- *; rewrite Rinv_mult_distr;
          [ ring | discrR | apply Rabs_no_R0; assumption ] ]
      | apply Rabs_no_R0; assumption ].
Qed.

Lemma RiemannInt_P11 :
  forall (f:R -> R) (a b l:R) (un:nat -> posreal)
    (phi1 phi2 psi1 psi2:nat -> StepFun a b),
    Un_cv un 0 ->
    (forall n:nat,
      (forall t:R,
        Rmin a b <= t <= Rmax a b -> Rabs (f t - phi1 n t) <= psi1 n t) /\
      Rabs (RiemannInt_SF (psi1 n)) < un n) ->
    (forall n:nat,
      (forall t:R,
        Rmin a b <= t <= Rmax a b -> Rabs (f t - phi2 n t) <= psi2 n t) /\
      Rabs (RiemannInt_SF (psi2 n)) < un n) ->
    Un_cv (fun N:nat => RiemannInt_SF (phi1 N)) l ->
    Un_cv (fun N:nat => RiemannInt_SF (phi2 N)) l.
Proof.
  unfold Un_cv in |- *; intro f; intros; intros.
  case (Rle_dec a b); intro Hyp.
  assert (H4 : 0 < eps / 3).
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ assumption | apply Rinv_0_lt_compat; prove_sup0 ].
  elim (H _ H4); clear H; intros N0 H.
  elim (H2 _ H4); clear H2; intros N1 H2.
  set (N := max N0 N1); exists N; intros; unfold R_dist in |- *.
  apply Rle_lt_trans with
    (Rabs (RiemannInt_SF (phi2 n) - RiemannInt_SF (phi1 n)) +
      Rabs (RiemannInt_SF (phi1 n) - l)).
  replace (RiemannInt_SF (phi2 n) - l) with
  (RiemannInt_SF (phi2 n) - RiemannInt_SF (phi1 n) +
    (RiemannInt_SF (phi1 n) - l)); [ apply Rabs_triang | ring ].
  replace eps with (2 * (eps / 3) + eps / 3).
  apply Rplus_lt_compat.
  replace (RiemannInt_SF (phi2 n) - RiemannInt_SF (phi1 n)) with
  (RiemannInt_SF (phi2 n) + -1 * RiemannInt_SF (phi1 n)); 
  [ idtac | ring ].
  rewrite <- StepFun_P30.
  apply Rle_lt_trans with
    (RiemannInt_SF
      (mkStepFun (StepFun_P32 (mkStepFun (StepFun_P28 (-1) (phi2 n) (phi1 n)))))).
  apply StepFun_P34; assumption.
  apply Rle_lt_trans with
    (RiemannInt_SF (mkStepFun (StepFun_P28 1 (psi1 n) (psi2 n)))).
  apply StepFun_P37; try assumption; intros; simpl in |- *; rewrite Rmult_1_l.
  apply Rle_trans with (Rabs (phi2 n x - f x) + Rabs (f x - phi1 n x)).
  replace (phi2 n x + -1 * phi1 n x) with (phi2 n x - f x + (f x - phi1 n x));
  [ apply Rabs_triang | ring ].
  rewrite (Rplus_comm (psi1 n x)); apply Rplus_le_compat.
  rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr; elim (H1 n); intros; apply H7.
  assert (H10 : Rmin a b = a).
  unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n0; assumption ].
  assert (H11 : Rmax a b = b).
  unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n0; assumption ].
  rewrite H10; rewrite H11; elim H6; intros; split; left; assumption.
  elim (H0 n); intros; apply H7; assert (H10 : Rmin a b = a).
  unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n0; assumption ].
  assert (H11 : Rmax a b = b).
  unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n0; assumption ].
  rewrite H10; rewrite H11; elim H6; intros; split; left; assumption.
  rewrite StepFun_P30; rewrite Rmult_1_l; rewrite double; apply Rplus_lt_compat.
  apply Rlt_trans with (pos (un n)).
  elim (H0 n); intros; apply Rle_lt_trans with (Rabs (RiemannInt_SF (psi1 n))).
  apply RRle_abs.
  assumption.
  replace (pos (un n)) with (R_dist (un n) 0).
  apply H; unfold ge in |- *; apply le_trans with N; try assumption.
  unfold N in |- *; apply le_max_l.
  unfold R_dist in |- *; unfold Rminus in |- *; rewrite Ropp_0;
    rewrite Rplus_0_r; apply Rabs_right.
  apply Rle_ge; left; apply (cond_pos (un n)).
  apply Rlt_trans with (pos (un n)).
  elim (H1 n); intros; apply Rle_lt_trans with (Rabs (RiemannInt_SF (psi2 n))).
  apply RRle_abs; assumption.
  assumption.
  replace (pos (un n)) with (R_dist (un n) 0).
  apply H; unfold ge in |- *; apply le_trans with N; try assumption;
    unfold N in |- *; apply le_max_l.
  unfold R_dist in |- *; unfold Rminus in |- *; rewrite Ropp_0;
    rewrite Rplus_0_r; apply Rabs_right; apply Rle_ge; 
      left; apply (cond_pos (un n)).
  unfold R_dist in H2; apply H2; unfold ge in |- *; apply le_trans with N;
    try assumption; unfold N in |- *; apply le_max_r.
  apply Rmult_eq_reg_l with 3;
    [ unfold Rdiv in |- *; rewrite Rmult_plus_distr_l;
      do 2 rewrite (Rmult_comm 3); repeat rewrite Rmult_assoc;
        rewrite <- Rinv_l_sym; [ ring | discrR ]
      | discrR ].
  assert (H4 : 0 < eps / 3).
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ assumption | apply Rinv_0_lt_compat; prove_sup0 ].
  elim (H _ H4); clear H; intros N0 H.
  elim (H2 _ H4); clear H2; intros N1 H2.
  set (N := max N0 N1); exists N; intros; unfold R_dist in |- *.
  apply Rle_lt_trans with
    (Rabs (RiemannInt_SF (phi2 n) - RiemannInt_SF (phi1 n)) +
      Rabs (RiemannInt_SF (phi1 n) - l)).
  replace (RiemannInt_SF (phi2 n) - l) with
  (RiemannInt_SF (phi2 n) - RiemannInt_SF (phi1 n) +
    (RiemannInt_SF (phi1 n) - l)); [ apply Rabs_triang | ring ].
  assert (Hyp_b : b <= a).
  auto with real.
  replace eps with (2 * (eps / 3) + eps / 3).
  apply Rplus_lt_compat.
  replace (RiemannInt_SF (phi2 n) - RiemannInt_SF (phi1 n)) with
  (RiemannInt_SF (phi2 n) + -1 * RiemannInt_SF (phi1 n)); 
  [ idtac | ring ].
  rewrite <- StepFun_P30.
  rewrite StepFun_P39.
  rewrite Rabs_Ropp.
  apply Rle_lt_trans with
    (RiemannInt_SF
      (mkStepFun
        (StepFun_P32
          (mkStepFun
            (StepFun_P6
              (pre (mkStepFun (StepFun_P28 (-1) (phi2 n) (phi1 n))))))))).
  apply StepFun_P34; try assumption.
  apply Rle_lt_trans with
    (RiemannInt_SF
      (mkStepFun
        (StepFun_P6 (pre (mkStepFun (StepFun_P28 1 (psi1 n) (psi2 n))))))).
  apply StepFun_P37; try assumption.
  intros; simpl in |- *; rewrite Rmult_1_l.
  apply Rle_trans with (Rabs (phi2 n x - f x) + Rabs (f x - phi1 n x)).
  replace (phi2 n x + -1 * phi1 n x) with (phi2 n x - f x + (f x - phi1 n x));
  [ apply Rabs_triang | ring ].
  rewrite (Rplus_comm (psi1 n x)); apply Rplus_le_compat.
  rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr; elim (H1 n); intros; apply H7.
  assert (H10 : Rmin a b = b).
  unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ elim Hyp; assumption | reflexivity ].
  assert (H11 : Rmax a b = a).
  unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ elim Hyp; assumption | reflexivity ].
  rewrite H10; rewrite H11; elim H6; intros; split; left; assumption.
  elim (H0 n); intros; apply H7; assert (H10 : Rmin a b = b).
  unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ elim Hyp; assumption | reflexivity ].
  assert (H11 : Rmax a b = a).
  unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ elim Hyp; assumption | reflexivity ].
  rewrite H10; rewrite H11; elim H6; intros; split; left; assumption.
  rewrite <-
    (Ropp_involutive
      (RiemannInt_SF
        (mkStepFun
          (StepFun_P6 (pre (mkStepFun (StepFun_P28 1 (psi1 n) (psi2 n))))))))
    .
  rewrite <- StepFun_P39.
  rewrite StepFun_P30.
  rewrite Rmult_1_l; rewrite double.
  rewrite Ropp_plus_distr; apply Rplus_lt_compat.
  apply Rlt_trans with (pos (un n)).
  elim (H0 n); intros; apply Rle_lt_trans with (Rabs (RiemannInt_SF (psi1 n))).
  rewrite <- Rabs_Ropp; apply RRle_abs.
  assumption.
  replace (pos (un n)) with (R_dist (un n) 0).
  apply H; unfold ge in |- *; apply le_trans with N; try assumption.
  unfold N in |- *; apply le_max_l.
  unfold R_dist in |- *; unfold Rminus in |- *; rewrite Ropp_0;
    rewrite Rplus_0_r; apply Rabs_right.
  apply Rle_ge; left; apply (cond_pos (un n)).
  apply Rlt_trans with (pos (un n)).
  elim (H1 n); intros; apply Rle_lt_trans with (Rabs (RiemannInt_SF (psi2 n))).
  rewrite <- Rabs_Ropp; apply RRle_abs; assumption.
  assumption.
  replace (pos (un n)) with (R_dist (un n) 0).
  apply H; unfold ge in |- *; apply le_trans with N; try assumption;
    unfold N in |- *; apply le_max_l.
  unfold R_dist in |- *; unfold Rminus in |- *; rewrite Ropp_0;
    rewrite Rplus_0_r; apply Rabs_right; apply Rle_ge; 
      left; apply (cond_pos (un n)).
  unfold R_dist in H2; apply H2; unfold ge in |- *; apply le_trans with N;
    try assumption; unfold N in |- *; apply le_max_r.
  apply Rmult_eq_reg_l with 3;
    [ unfold Rdiv in |- *; rewrite Rmult_plus_distr_l;
      do 2 rewrite (Rmult_comm 3); repeat rewrite Rmult_assoc;
        rewrite <- Rinv_l_sym; [ ring | discrR ]
      | discrR ].
Qed.

Lemma RiemannInt_P12 :
  forall (f g:R -> R) (a b l:R) (pr1:Riemann_integrable f a b)
    (pr2:Riemann_integrable g a b)
    (pr3:Riemann_integrable (fun x:R => f x + l * g x) a b),
    a <= b -> RiemannInt pr3 = RiemannInt pr1 + l * RiemannInt pr2.
Proof.
  intro f; intros; case (Req_dec l 0); intro.
  pattern l at 2 in |- *; rewrite H0; rewrite Rmult_0_l; rewrite Rplus_0_r;
    unfold RiemannInt in |- *; case (RiemannInt_exists pr3 RinvN RinvN_cv);
      case (RiemannInt_exists pr1 RinvN RinvN_cv); intros; 
        eapply UL_sequence;
          [ apply u0
            | set (psi1 := fun n:nat => projT1 (phi_sequence_prop RinvN pr1 n));
              set (psi2 := fun n:nat => projT1 (phi_sequence_prop RinvN pr3 n));
                apply RiemannInt_P11 with f RinvN (phi_sequence RinvN pr1) psi1 psi2;
                  [ apply RinvN_cv
                    | intro; apply (projT2 (phi_sequence_prop RinvN pr1 n))
                    | intro;
                      assert
                        (H1 :
                          (forall t:R,
                            Rmin a b <= t /\ t <= Rmax a b ->
                            Rabs (f t + l * g t - phi_sequence RinvN pr3 n t) <= psi2 n t) /\
                          Rabs (RiemannInt_SF (psi2 n)) < RinvN n);
                        [ apply (projT2 (phi_sequence_prop RinvN pr3 n))
                          | elim H1; intros; split; try assumption; intros;
                            replace (f t) with (f t + l * g t);
                            [ apply H2; assumption | rewrite H0; ring ] ]
                    | assumption ] ].
  eapply UL_sequence.
  unfold RiemannInt in |- *; case (RiemannInt_exists pr3 RinvN RinvN_cv);
    intros; apply u.
  unfold Un_cv in |- *; intros; unfold RiemannInt in |- *;
    case (RiemannInt_exists pr1 RinvN RinvN_cv);
    case (RiemannInt_exists pr2 RinvN RinvN_cv); unfold Un_cv in |- *; 
      intros; assert (H2 : 0 < eps / 5).
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ assumption | apply Rinv_0_lt_compat; prove_sup0 ].
  elim (u0 _ H2); clear u0; intros N0 H3; assert (H4 := RinvN_cv);
    unfold Un_cv in H4; elim (H4 _ H2); clear H4 H2; intros N1 H4;
      assert (H5 : 0 < eps / (5 * Rabs l)). 
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ assumption
      | apply Rinv_0_lt_compat; apply Rmult_lt_0_compat;
        [ prove_sup0 | apply Rabs_pos_lt; assumption ] ].
  elim (u _ H5); clear u; intros N2 H6; assert (H7 := RinvN_cv);
    unfold Un_cv in H7; elim (H7 _ H5); clear H7 H5; intros N3 H5;
      unfold R_dist in H3, H4, H5, H6; set (N := max (max N0 N1) (max N2 N3)).
  assert (H7 : forall n:nat, (n >= N1)%nat -> RinvN n < eps / 5).
  intros; replace (pos (RinvN n)) with (Rabs (RinvN n - 0));
    [ unfold RinvN in |- *; apply H4; assumption
      | unfold Rminus in |- *; rewrite Ropp_0; rewrite Rplus_0_r; apply Rabs_right;
        left; apply (cond_pos (RinvN n)) ].
  clear H4; assert (H4 := H7); clear H7;
    assert (H7 : forall n:nat, (n >= N3)%nat -> RinvN n < eps / (5 * Rabs l)).
  intros; replace (pos (RinvN n)) with (Rabs (RinvN n - 0));
    [ unfold RinvN in |- *; apply H5; assumption
      | unfold Rminus in |- *; rewrite Ropp_0; rewrite Rplus_0_r; apply Rabs_right;
        left; apply (cond_pos (RinvN n)) ].
  clear H5; assert (H5 := H7); clear H7; exists N; intros;
    unfold R_dist in |- *.
  apply Rle_lt_trans with
    (Rabs
      (RiemannInt_SF (phi_sequence RinvN pr3 n) -
        (RiemannInt_SF (phi_sequence RinvN pr1 n) +
          l * RiemannInt_SF (phi_sequence RinvN pr2 n))) +
      Rabs (RiemannInt_SF (phi_sequence RinvN pr1 n) - x0) +
      Rabs l * Rabs (RiemannInt_SF (phi_sequence RinvN pr2 n) - x)).
  apply Rle_trans with
    (Rabs
      (RiemannInt_SF (phi_sequence RinvN pr3 n) -
        (RiemannInt_SF (phi_sequence RinvN pr1 n) +
          l * RiemannInt_SF (phi_sequence RinvN pr2 n))) +
      Rabs
      (RiemannInt_SF (phi_sequence RinvN pr1 n) - x0 +
        l * (RiemannInt_SF (phi_sequence RinvN pr2 n) - x))).
  replace (RiemannInt_SF (phi_sequence RinvN pr3 n) - (x0 + l * x)) with
  (RiemannInt_SF (phi_sequence RinvN pr3 n) -
    (RiemannInt_SF (phi_sequence RinvN pr1 n) +
      l * RiemannInt_SF (phi_sequence RinvN pr2 n)) +
    (RiemannInt_SF (phi_sequence RinvN pr1 n) - x0 +
      l * (RiemannInt_SF (phi_sequence RinvN pr2 n) - x)));
  [ apply Rabs_triang | ring ].
  rewrite Rplus_assoc; apply Rplus_le_compat_l; rewrite <- Rabs_mult;
    replace
    (RiemannInt_SF (phi_sequence RinvN pr1 n) - x0 +
      l * (RiemannInt_SF (phi_sequence RinvN pr2 n) - x)) with
    (RiemannInt_SF (phi_sequence RinvN pr1 n) - x0 +
      l * (RiemannInt_SF (phi_sequence RinvN pr2 n) - x));
    [ apply Rabs_triang | ring ].
  replace eps with (3 * (eps / 5) + eps / 5 + eps / 5).
  repeat apply Rplus_lt_compat.
  assert
    (H7 :
      exists psi1 : nat -> StepFun a b,
        (forall n:nat,
          (forall t:R,
            Rmin a b <= t /\ t <= Rmax a b ->
            Rabs (f t - phi_sequence RinvN pr1 n t) <= psi1 n t) /\
          Rabs (RiemannInt_SF (psi1 n)) < RinvN n)).
  split with (fun n:nat => projT1 (phi_sequence_prop RinvN pr1 n)); intro;
    apply (projT2 (phi_sequence_prop RinvN pr1 n0)).
  assert
    (H8 :
      exists psi2 : nat -> StepFun a b,
        (forall n:nat,
          (forall t:R,
            Rmin a b <= t /\ t <= Rmax a b ->
            Rabs (g t - phi_sequence RinvN pr2 n t) <= psi2 n t) /\
          Rabs (RiemannInt_SF (psi2 n)) < RinvN n)).
  split with (fun n:nat => projT1 (phi_sequence_prop RinvN pr2 n)); intro;
    apply (projT2 (phi_sequence_prop RinvN pr2 n0)).
  assert
    (H9 :
      exists psi3 : nat -> StepFun a b,
        (forall n:nat,
          (forall t:R,
            Rmin a b <= t /\ t <= Rmax a b ->
            Rabs (f t + l * g t - phi_sequence RinvN pr3 n t) <= psi3 n t) /\
          Rabs (RiemannInt_SF (psi3 n)) < RinvN n)).
  split with (fun n:nat => projT1 (phi_sequence_prop RinvN pr3 n)); intro;
    apply (projT2 (phi_sequence_prop RinvN pr3 n0)).
  elim H7; clear H7; intros psi1 H7; elim H8; clear H8; intros psi2 H8; elim H9;
    clear H9; intros psi3 H9;
      replace
      (RiemannInt_SF (phi_sequence RinvN pr3 n) -
        (RiemannInt_SF (phi_sequence RinvN pr1 n) +
          l * RiemannInt_SF (phi_sequence RinvN pr2 n))) with
      (RiemannInt_SF (phi_sequence RinvN pr3 n) +
        -1 *
        (RiemannInt_SF (phi_sequence RinvN pr1 n) +
          l * RiemannInt_SF (phi_sequence RinvN pr2 n))); 
      [ idtac | ring ]; do 2 rewrite <- StepFun_P30; assert (H10 : Rmin a b = a).
  unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n0; assumption ].
  assert (H11 : Rmax a b = b).
  unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n0; assumption ].
  rewrite H10 in H7; rewrite H10 in H8; rewrite H10 in H9; rewrite H11 in H7;
    rewrite H11 in H8; rewrite H11 in H9;
      apply Rle_lt_trans with
        (RiemannInt_SF
          (mkStepFun
            (StepFun_P32
              (mkStepFun
                (StepFun_P28 (-1) (phi_sequence RinvN pr3 n)
                  (mkStepFun
                    (StepFun_P28 l (phi_sequence RinvN pr1 n)
                      (phi_sequence RinvN pr2 n)))))))).
  apply StepFun_P34; assumption.
  apply Rle_lt_trans with
    (RiemannInt_SF
      (mkStepFun
        (StepFun_P28 1 (psi3 n)
          (mkStepFun (StepFun_P28 (Rabs l) (psi1 n) (psi2 n)))))).
  apply StepFun_P37; try assumption.
  intros; simpl in |- *; rewrite Rmult_1_l.
  apply Rle_trans with
    (Rabs (phi_sequence RinvN pr3 n x1 - (f x1 + l * g x1)) +
      Rabs
      (f x1 + l * g x1 +
        -1 * (phi_sequence RinvN pr1 n x1 + l * phi_sequence RinvN pr2 n x1))).
  replace
  (phi_sequence RinvN pr3 n x1 +
    -1 * (phi_sequence RinvN pr1 n x1 + l * phi_sequence RinvN pr2 n x1)) with
  (phi_sequence RinvN pr3 n x1 - (f x1 + l * g x1) +
    (f x1 + l * g x1 +
      -1 * (phi_sequence RinvN pr1 n x1 + l * phi_sequence RinvN pr2 n x1)));
  [ apply Rabs_triang | ring ].
  rewrite Rplus_assoc; apply Rplus_le_compat.
  elim (H9 n); intros; rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr;
    apply H13.
  elim H12; intros; split; left; assumption. 
  apply Rle_trans with
    (Rabs (f x1 - phi_sequence RinvN pr1 n x1) +
      Rabs l * Rabs (g x1 - phi_sequence RinvN pr2 n x1)).
  rewrite <- Rabs_mult;
    replace
    (f x1 +
      (l * g x1 +
        -1 * (phi_sequence RinvN pr1 n x1 + l * phi_sequence RinvN pr2 n x1)))
    with
      (f x1 - phi_sequence RinvN pr1 n x1 +
        l * (g x1 - phi_sequence RinvN pr2 n x1)); [ apply Rabs_triang | ring ].
  apply Rplus_le_compat.
  elim (H7 n); intros; apply H13.
  elim H12; intros; split; left; assumption.
  apply Rmult_le_compat_l;
    [ apply Rabs_pos
      | elim (H8 n); intros; apply H13; elim H12; intros; split; left; assumption ].
  do 2 rewrite StepFun_P30; rewrite Rmult_1_l;
    replace (3 * (eps / 5)) with (eps / 5 + (eps / 5 + eps / 5));
    [ repeat apply Rplus_lt_compat | ring ].
  apply Rlt_trans with (pos (RinvN n));
    [ apply Rle_lt_trans with (Rabs (RiemannInt_SF (psi3 n)));
      [ apply RRle_abs | elim (H9 n); intros; assumption ]
      | apply H4; unfold ge in |- *; apply le_trans with N;
        [ apply le_trans with (max N0 N1);
          [ apply le_max_r | unfold N in |- *; apply le_max_l ]
          | assumption ] ].
  apply Rlt_trans with (pos (RinvN n));
    [ apply Rle_lt_trans with (Rabs (RiemannInt_SF (psi1 n)));
      [ apply RRle_abs | elim (H7 n); intros; assumption ]
      | apply H4; unfold ge in |- *; apply le_trans with N;
        [ apply le_trans with (max N0 N1);
          [ apply le_max_r | unfold N in |- *; apply le_max_l ]
          | assumption ] ].
  apply Rmult_lt_reg_l with (/ Rabs l).
  apply Rinv_0_lt_compat; apply Rabs_pos_lt; assumption.
  rewrite <- Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_l; replace (/ Rabs l * (eps / 5)) with (eps / (5 * Rabs l)).
  apply Rlt_trans with (pos (RinvN n));
    [ apply Rle_lt_trans with (Rabs (RiemannInt_SF (psi2 n)));
      [ apply RRle_abs | elim (H8 n); intros; assumption ]
      | apply H5; unfold ge in |- *; apply le_trans with N;
        [ apply le_trans with (max N2 N3);
          [ apply le_max_r | unfold N in |- *; apply le_max_r ]
          | assumption ] ].
  unfold Rdiv in |- *; rewrite Rinv_mult_distr;
    [ ring | discrR | apply Rabs_no_R0; assumption ].
  apply Rabs_no_R0; assumption.
  apply H3; unfold ge in |- *; apply le_trans with (max N0 N1);
    [ apply le_max_l
      | apply le_trans with N; [ unfold N in |- *; apply le_max_l | assumption ] ].
  apply Rmult_lt_reg_l with (/ Rabs l).
  apply Rinv_0_lt_compat; apply Rabs_pos_lt; assumption.
  rewrite <- Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_l; replace (/ Rabs l * (eps / 5)) with (eps / (5 * Rabs l)).
  apply H6; unfold ge in |- *; apply le_trans with (max N2 N3);
    [ apply le_max_l
      | apply le_trans with N; [ unfold N in |- *; apply le_max_r | assumption ] ].
  unfold Rdiv in |- *; rewrite Rinv_mult_distr;
    [ ring | discrR | apply Rabs_no_R0; assumption ].
  apply Rabs_no_R0; assumption.
  apply Rmult_eq_reg_l with 5;
    [ unfold Rdiv in |- *; do 2 rewrite Rmult_plus_distr_l;
      do 3 rewrite (Rmult_comm 5); repeat rewrite Rmult_assoc;
        rewrite <- Rinv_l_sym; [ ring | discrR ]
      | discrR ]. 
Qed.

Lemma RiemannInt_P13 :
  forall (f g:R -> R) (a b l:R) (pr1:Riemann_integrable f a b)
    (pr2:Riemann_integrable g a b)
    (pr3:Riemann_integrable (fun x:R => f x + l * g x) a b),
    RiemannInt pr3 = RiemannInt pr1 + l * RiemannInt pr2.
Proof.
  intros; case (Rle_dec a b); intro;
    [ apply RiemannInt_P12; assumption
      | assert (H : b <= a);
        [ auto with real
          | replace (RiemannInt pr3) with (- RiemannInt (RiemannInt_P1 pr3));
            [ idtac | symmetry  in |- *; apply RiemannInt_P8 ];
            replace (RiemannInt pr2) with (- RiemannInt (RiemannInt_P1 pr2));
            [ idtac | symmetry  in |- *; apply RiemannInt_P8 ];
            replace (RiemannInt pr1) with (- RiemannInt (RiemannInt_P1 pr1));
            [ idtac | symmetry  in |- *; apply RiemannInt_P8 ];
            rewrite
              (RiemannInt_P12 (RiemannInt_P1 pr1) (RiemannInt_P1 pr2)
                (RiemannInt_P1 pr3) H); ring ] ].
Qed.

Lemma RiemannInt_P14 : forall a b c:R, Riemann_integrable (fct_cte c) a b.
Proof.
  unfold Riemann_integrable in |- *; intros;
    split with (mkStepFun (StepFun_P4 a b c));
      split with (mkStepFun (StepFun_P4 a b 0)); split;
        [ intros; simpl in |- *; unfold Rminus in |- *; rewrite Rplus_opp_r;
          rewrite Rabs_R0; unfold fct_cte in |- *; right; 
            reflexivity
          | rewrite StepFun_P18; rewrite Rmult_0_l; rewrite Rabs_R0;
            apply (cond_pos eps) ].
Qed.

Lemma RiemannInt_P15 :
  forall (a b c:R) (pr:Riemann_integrable (fct_cte c) a b),
    RiemannInt pr = c * (b - a).
Proof.
  intros; unfold RiemannInt in |- *; case (RiemannInt_exists pr RinvN RinvN_cv);
    intros; eapply UL_sequence.
  apply u.
  set (phi1 := fun N:nat => phi_sequence RinvN pr N);
    change (Un_cv (fun N:nat => RiemannInt_SF (phi1 N)) (c * (b - a))) in |- *;
      set (f := fct_cte c);
        assert
          (H1 :
            exists psi1 : nat -> StepFun a b,
              (forall n:nat,
                (forall t:R,
                  Rmin a b <= t /\ t <= Rmax a b ->
                  Rabs (f t - phi_sequence RinvN pr n t) <= psi1 n t) /\
                Rabs (RiemannInt_SF (psi1 n)) < RinvN n)).
  split with (fun n:nat => projT1 (phi_sequence_prop RinvN pr n)); intro;
    apply (projT2 (phi_sequence_prop RinvN pr n)).
  elim H1; clear H1; intros psi1 H1;
    set (phi2 := fun n:nat => mkStepFun (StepFun_P4 a b c));
      set (psi2 := fun n:nat => mkStepFun (StepFun_P4 a b 0));
        apply RiemannInt_P11 with f RinvN phi2 psi2 psi1; 
          try assumption.
  apply RinvN_cv.
  intro; split.
  intros; unfold f in |- *; simpl in |- *; unfold Rminus in |- *;
    rewrite Rplus_opp_r; rewrite Rabs_R0; unfold fct_cte in |- *; 
      right; reflexivity.
  unfold psi2 in |- *; rewrite StepFun_P18; rewrite Rmult_0_l; rewrite Rabs_R0;
    apply (cond_pos (RinvN n)).
  unfold Un_cv in |- *; intros; split with 0%nat; intros; unfold R_dist in |- *;
    unfold phi2 in |- *; rewrite StepFun_P18; unfold Rminus in |- *;
      rewrite Rplus_opp_r; rewrite Rabs_R0; apply H.
Qed.

Lemma RiemannInt_P16 :
  forall (f:R -> R) (a b:R),
    Riemann_integrable f a b -> Riemann_integrable (fun x:R => Rabs (f x)) a b.
Proof.
  unfold Riemann_integrable in |- *; intro f; intros; elim (X eps); clear X;
    intros phi [psi [H H0]]; split with (mkStepFun (StepFun_P32 phi));
      split with psi; split; try assumption; intros; simpl in |- *;
        apply Rle_trans with (Rabs (f t - phi t));
          [ apply Rabs_triang_inv2 | apply H; assumption ].
Qed.

Lemma Rle_cv_lim :
  forall (Un Vn:nat -> R) (l1 l2:R),
    (forall n:nat, Un n <= Vn n) -> Un_cv Un l1 -> Un_cv Vn l2 -> l1 <= l2.
Proof.
  intros; case (Rle_dec l1 l2); intro.
  assumption.
  assert (H2 : l2 < l1).
  auto with real.
  clear n; assert (H3 : 0 < (l1 - l2) / 2).
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ apply Rlt_Rminus; assumption | apply Rinv_0_lt_compat; prove_sup0 ].
  elim (H1 _ H3); elim (H0 _ H3); clear H0 H1; unfold R_dist in |- *; intros;
    set (N := max x x0); cut (Vn N < Un N).
  intro; elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ (H N) H4)).
  apply Rlt_trans with ((l1 + l2) / 2).
  apply Rplus_lt_reg_r with (- l2);
    replace (- l2 + (l1 + l2) / 2) with ((l1 - l2) / 2).
  rewrite Rplus_comm; apply Rle_lt_trans with (Rabs (Vn N - l2)).
  apply RRle_abs.
  apply H1; unfold ge in |- *; unfold N in |- *; apply le_max_r.
  apply Rmult_eq_reg_l with 2;
    [ unfold Rdiv in |- *; do 2 rewrite (Rmult_comm 2);
      rewrite (Rmult_plus_distr_r (- l2) ((l1 + l2) * / 2) 2);
        repeat rewrite Rmult_assoc; rewrite <- Rinv_l_sym; 
          [ ring | discrR ]
      | discrR ].
  apply Ropp_lt_cancel; apply Rplus_lt_reg_r with l1;
    replace (l1 + - ((l1 + l2) / 2)) with ((l1 - l2) / 2).
  apply Rle_lt_trans with (Rabs (Un N - l1)).
  rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr; apply RRle_abs.
  apply H0; unfold ge in |- *; unfold N in |- *; apply le_max_l.
  apply Rmult_eq_reg_l with 2;
    [ unfold Rdiv in |- *; do 2 rewrite (Rmult_comm 2);
      rewrite (Rmult_plus_distr_r l1 (- ((l1 + l2) * / 2)) 2);
        rewrite <- Ropp_mult_distr_l_reverse; repeat rewrite Rmult_assoc;
          rewrite <- Rinv_l_sym; [ ring | discrR ]
      | discrR ].
Qed.

Lemma RiemannInt_P17 :
  forall (f:R -> R) (a b:R) (pr1:Riemann_integrable f a b)
    (pr2:Riemann_integrable (fun x:R => Rabs (f x)) a b),
    a <= b -> Rabs (RiemannInt pr1) <= RiemannInt pr2.
Proof.
  intro f; intros; unfold RiemannInt in |- *;
    case (RiemannInt_exists pr1 RinvN RinvN_cv);
    case (RiemannInt_exists pr2 RinvN RinvN_cv); intros;
      set (phi1 := phi_sequence RinvN pr1) in u0;
        set (phi2 := fun N:nat => mkStepFun (StepFun_P32 (phi1 N)));
          apply Rle_cv_lim with
            (fun N:nat => Rabs (RiemannInt_SF (phi1 N)))
            (fun N:nat => RiemannInt_SF (phi2 N)).
  intro; unfold phi2 in |- *; apply StepFun_P34; assumption.
  apply (continuity_seq Rabs (fun N:nat => RiemannInt_SF (phi1 N)) x0);
    try assumption.
  apply Rcontinuity_abs.
  set (phi3 := phi_sequence RinvN pr2);
    assert
      (H0 :
        exists psi3 : nat -> StepFun a b,
          (forall n:nat,
            (forall t:R,
              Rmin a b <= t /\ t <= Rmax a b ->
              Rabs (Rabs (f t) - phi3 n t) <= psi3 n t) /\
            Rabs (RiemannInt_SF (psi3 n)) < RinvN n)).
  split with (fun n:nat => projT1 (phi_sequence_prop RinvN pr2 n)); intro;
    apply (projT2 (phi_sequence_prop RinvN pr2 n)). 
  assert
    (H1 :
      exists psi2 : nat -> StepFun a b,
        (forall n:nat,
          (forall t:R,
            Rmin a b <= t /\ t <= Rmax a b ->
            Rabs (Rabs (f t) - phi2 n t) <= psi2 n t) /\
          Rabs (RiemannInt_SF (psi2 n)) < RinvN n)).
  assert
    (H1 :
      exists psi2 : nat -> StepFun a b,
        (forall n:nat,
          (forall t:R,
            Rmin a b <= t /\ t <= Rmax a b -> Rabs (f t - phi1 n t) <= psi2 n t) /\
          Rabs (RiemannInt_SF (psi2 n)) < RinvN n)).
  split with (fun n:nat => projT1 (phi_sequence_prop RinvN pr1 n)); intro;
    apply (projT2 (phi_sequence_prop RinvN pr1 n)).
  elim H1; clear H1; intros psi2 H1; split with psi2; intros; elim (H1 n);
    clear H1; intros; split; try assumption.
  intros; unfold phi2 in |- *; simpl in |- *;
    apply Rle_trans with (Rabs (f t - phi1 n t)).
  apply Rabs_triang_inv2.
  apply H1; assumption.
  elim H0; clear H0; intros psi3 H0; elim H1; clear H1; intros psi2 H1;
    apply RiemannInt_P11 with (fun x:R => Rabs (f x)) RinvN phi3 psi3 psi2;
      try assumption; apply RinvN_cv.
Qed.

Lemma RiemannInt_P18 :
  forall (f g:R -> R) (a b:R) (pr1:Riemann_integrable f a b)
    (pr2:Riemann_integrable g a b),
    a <= b ->
    (forall x:R, a < x < b -> f x = g x) -> RiemannInt pr1 = RiemannInt pr2.
Proof.
  intro f; intros; unfold RiemannInt in |- *;
    case (RiemannInt_exists pr1 RinvN RinvN_cv);
    case (RiemannInt_exists pr2 RinvN RinvN_cv); intros; 
      eapply UL_sequence.
  apply u0.
  set (phi1 := fun N:nat => phi_sequence RinvN pr1 N);
    change (Un_cv (fun N:nat => RiemannInt_SF (phi1 N)) x) in |- *;
      assert
        (H1 :
          exists psi1 : nat -> StepFun a b,
            (forall n:nat,
              (forall t:R,
                Rmin a b <= t /\ t <= Rmax a b ->
                Rabs (f t - phi1 n t) <= psi1 n t) /\
              Rabs (RiemannInt_SF (psi1 n)) < RinvN n)).
  split with (fun n:nat => projT1 (phi_sequence_prop RinvN pr1 n)); intro;
    apply (projT2 (phi_sequence_prop RinvN pr1 n)). 
  elim H1; clear H1; intros psi1 H1;
    set (phi2 := fun N:nat => phi_sequence RinvN pr2 N).
  set
    (phi2_aux :=
      fun (N:nat) (x:R) =>
        match Req_EM_T x a with
          | left _ => f a
          | right _ =>
            match Req_EM_T x b with
              | left _ => f b
              | right _ => phi2 N x
            end
        end).
  cut (forall N:nat, IsStepFun (phi2_aux N) a b).
  intro; set (phi2_m := fun N:nat => mkStepFun (X N)).
  assert
    (H2 :
      exists psi2 : nat -> StepFun a b,
        (forall n:nat,
          (forall t:R,
            Rmin a b <= t /\ t <= Rmax a b -> Rabs (g t - phi2 n t) <= psi2 n t) /\
          Rabs (RiemannInt_SF (psi2 n)) < RinvN n)).
  split with (fun n:nat => projT1 (phi_sequence_prop RinvN pr2 n)); intro;
    apply (projT2 (phi_sequence_prop RinvN pr2 n)). 
  elim H2; clear H2; intros psi2 H2;
    apply RiemannInt_P11 with f RinvN phi2_m psi2 psi1; 
      try assumption. 
  apply RinvN_cv.
  intro; elim (H2 n); intros; split; try assumption.
  intros; unfold phi2_m in |- *; simpl in |- *; unfold phi2_aux in |- *;
    case (Req_EM_T t a); case (Req_EM_T t b); intros.
  rewrite e0; unfold Rminus in |- *; rewrite Rplus_opp_r; rewrite Rabs_R0;
    apply Rle_trans with (Rabs (g t - phi2 n t)).
  apply Rabs_pos.
  pattern a at 3 in |- *; rewrite <- e0; apply H3; assumption.
  rewrite e; unfold Rminus in |- *; rewrite Rplus_opp_r; rewrite Rabs_R0;
    apply Rle_trans with (Rabs (g t - phi2 n t)).
  apply Rabs_pos.
  pattern a at 3 in |- *; rewrite <- e; apply H3; assumption.
  rewrite e; unfold Rminus in |- *; rewrite Rplus_opp_r; rewrite Rabs_R0;
    apply Rle_trans with (Rabs (g t - phi2 n t)).
  apply Rabs_pos.
  pattern b at 3 in |- *; rewrite <- e; apply H3; assumption.
  replace (f t) with (g t).
  apply H3; assumption.
  symmetry  in |- *; apply H0; elim H5; clear H5; intros.
  assert (H7 : Rmin a b = a).
  unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n2; assumption ].
  assert (H8 : Rmax a b = b).
  unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n2; assumption ].
  rewrite H7 in H5; rewrite H8 in H6; split.
  elim H5; intro; [ assumption | elim n1; symmetry  in |- *; assumption ].
  elim H6; intro; [ assumption | elim n0; assumption ].
  cut (forall N:nat, RiemannInt_SF (phi2_m N) = RiemannInt_SF (phi2 N)).
  intro; unfold Un_cv in |- *; intros; elim (u _ H4); intros; exists x1; intros;
    rewrite (H3 n); apply H5; assumption.
  intro; apply Rle_antisym.
  apply StepFun_P37; try assumption.
  intros; unfold phi2_m in |- *; simpl in |- *; unfold phi2_aux in |- *;
    case (Req_EM_T x1 a); case (Req_EM_T x1 b); intros.
  elim H3; intros; rewrite e0 in H4; elim (Rlt_irrefl _ H4).
  elim H3; intros; rewrite e in H4; elim (Rlt_irrefl _ H4).
  elim H3; intros; rewrite e in H5; elim (Rlt_irrefl _ H5).
  right; reflexivity.
  apply StepFun_P37; try assumption.
  intros; unfold phi2_m in |- *; simpl in |- *; unfold phi2_aux in |- *;
    case (Req_EM_T x1 a); case (Req_EM_T x1 b); intros.
  elim H3; intros; rewrite e0 in H4; elim (Rlt_irrefl _ H4).
  elim H3; intros; rewrite e in H4; elim (Rlt_irrefl _ H4).
  elim H3; intros; rewrite e in H5; elim (Rlt_irrefl _ H5).
  right; reflexivity.
  intro; assert (H2 := pre (phi2 N)); unfold IsStepFun in H2;
    unfold is_subdivision in H2; elim H2; clear H2; intros l [lf H2];
      split with l; split with lf; unfold adapted_couple in H2; 
        decompose [and] H2; clear H2; unfold adapted_couple in |- *; 
          repeat split; try assumption.
  intros; assert (H9 := H8 i H2); unfold constant_D_eq, open_interval in H9;
    unfold constant_D_eq, open_interval in |- *; intros; 
      rewrite <- (H9 x1 H7); assert (H10 : a <= pos_Rl l i).
  replace a with (Rmin a b).
  rewrite <- H5; elim (RList_P6 l); intros; apply H10.
  assumption.
  apply le_O_n.
  apply lt_trans with (pred (Rlength l)); [ assumption | apply lt_pred_n_n ].
  apply neq_O_lt; intro; rewrite <- H12 in H6; discriminate.
  unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; assumption ].
  assert (H11 : pos_Rl l (S i) <= b).
  replace b with (Rmax a b).
  rewrite <- H4; elim (RList_P6 l); intros; apply H11.
  assumption.
  apply lt_le_S; assumption.
  apply lt_pred_n_n; apply neq_O_lt; intro; rewrite <- H13 in H6; discriminate.
  unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; assumption ].
  elim H7; clear H7; intros; unfold phi2_aux in |- *; case (Req_EM_T x1 a);
    case (Req_EM_T x1 b); intros.
  rewrite e in H12; elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H11 H12)).
  rewrite e in H7; elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H10 H7)).
  rewrite e in H12; elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H11 H12)).
  reflexivity.
Qed.

Lemma RiemannInt_P19 :
  forall (f g:R -> R) (a b:R) (pr1:Riemann_integrable f a b)
    (pr2:Riemann_integrable g a b),
    a <= b ->
    (forall x:R, a < x < b -> f x <= g x) -> RiemannInt pr1 <= RiemannInt pr2.
Proof.
  intro f; intros; apply Rplus_le_reg_l with (- RiemannInt pr1);
    rewrite Rplus_opp_l; rewrite Rplus_comm;
      apply Rle_trans with (Rabs (RiemannInt (RiemannInt_P10 (-1) pr2 pr1))).
  apply Rabs_pos.
  replace (RiemannInt pr2 + - RiemannInt pr1) with
  (RiemannInt (RiemannInt_P16 (RiemannInt_P10 (-1) pr2 pr1))).
  apply
    (RiemannInt_P17 (RiemannInt_P10 (-1) pr2 pr1)
      (RiemannInt_P16 (RiemannInt_P10 (-1) pr2 pr1))); 
    assumption.
  replace (RiemannInt pr2 + - RiemannInt pr1) with
  (RiemannInt (RiemannInt_P10 (-1) pr2 pr1)).
  apply RiemannInt_P18; try assumption.
  intros; apply Rabs_right.
  apply Rle_ge; apply Rplus_le_reg_l with (f x); rewrite Rplus_0_r;
    replace (f x + (g x + -1 * f x)) with (g x); [ apply H0; assumption | ring ].
  rewrite (RiemannInt_P12 pr2 pr1 (RiemannInt_P10 (-1) pr2 pr1));
    [ ring | assumption ].
Qed.

Lemma FTC_P1 :
  forall (f:R -> R) (a b:R),
    a <= b ->
    (forall x:R, a <= x <= b -> continuity_pt f x) ->
    forall x:R, a <= x -> x <= b -> Riemann_integrable f a x.
Proof.
  intros; apply continuity_implies_RiemannInt;
    [ assumption
      | intros; apply H0; elim H3; intros; split;
        assumption || apply Rle_trans with x; assumption ].
Qed.

Definition primitive (f:R -> R) (a b:R) (h:a <= b)
  (pr:forall x:R, a <= x -> x <= b -> Riemann_integrable f a x) 
  (x:R) : R :=
  match Rle_dec a x with
    | left r =>
      match Rle_dec x b with
        | left r0 => RiemannInt (pr x r r0)
        | right _ => f b * (x - b) + RiemannInt (pr b h (Rle_refl b))
      end
    | right _ => f a * (x - a)
  end.

Lemma RiemannInt_P20 :
  forall (f:R -> R) (a b:R) (h:a <= b)
    (pr:forall x:R, a <= x -> x <= b -> Riemann_integrable f a x)
    (pr0:Riemann_integrable f a b),
    RiemannInt pr0 = primitive h pr b - primitive h pr a.
Proof.
  intros; replace (primitive h pr a) with 0.
  replace (RiemannInt pr0) with (primitive h pr b).
  ring.
  unfold primitive in |- *; case (Rle_dec a b); case (Rle_dec b b); intros;
    [ apply RiemannInt_P5
      | elim n; right; reflexivity
      | elim n; assumption
      | elim n0; assumption ].
  symmetry  in |- *; unfold primitive in |- *; case (Rle_dec a a);
    case (Rle_dec a b); intros;
      [ apply RiemannInt_P9
        | elim n; assumption
        | elim n; right; reflexivity
        | elim n0; right; reflexivity ].
Qed.

Lemma RiemannInt_P21 :
  forall (f:R -> R) (a b c:R),
    a <= b ->
    b <= c ->
    Riemann_integrable f a b ->
    Riemann_integrable f b c -> Riemann_integrable f a c.
Proof.
  unfold Riemann_integrable in |- *; intros f a b c Hyp1 Hyp2 X X0 eps.
  assert (H : 0 < eps / 2).
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ apply (cond_pos eps) | apply Rinv_0_lt_compat; prove_sup0 ].
  elim (X (mkposreal _ H)); clear X; intros phi1 [psi1 H1];
    elim (X0 (mkposreal _ H)); clear X0; intros phi2 [psi2 H2].
  set
    (phi3 :=
      fun x:R =>
        match Rle_dec a x with
          | left _ =>
            match Rle_dec x b with
              | left _ => phi1 x
              | right _ => phi2 x
            end
          | right _ => 0
        end).
  set
    (psi3 :=
      fun x:R =>
        match Rle_dec a x with
          | left _ =>
            match Rle_dec x b with
              | left _ => psi1 x
              | right _ => psi2 x
            end
          | right _ => 0
        end).
  cut (IsStepFun phi3 a c).
  intro; cut (IsStepFun psi3 a b).
  intro; cut (IsStepFun psi3 b c).
  intro; cut (IsStepFun psi3 a c).
  intro; split with (mkStepFun X); split with (mkStepFun X2); simpl in |- *;
    split.
  intros; unfold phi3, psi3 in |- *; case (Rle_dec t b); case (Rle_dec a t);
    intros.
  elim H1; intros; apply H3.
  replace (Rmin a b) with a.
  replace (Rmax a b) with b.
  split; assumption.
  unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; assumption ].
  unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; assumption ].
  elim n; replace a with (Rmin a c).
  elim H0; intros; assumption.
  unfold Rmin in |- *; case (Rle_dec a c); intro;
    [ reflexivity | elim n0; apply Rle_trans with b; assumption ].
  elim H2; intros; apply H3.
  replace (Rmax b c) with (Rmax a c).
  elim H0; intros; split; try assumption.
  replace (Rmin b c) with b.
  auto with real.
  unfold Rmin in |- *; case (Rle_dec b c); intro;
    [ reflexivity | elim n0; assumption ].
  unfold Rmax in |- *; case (Rle_dec a c); case (Rle_dec b c); intros;
    try (elim n0; assumption || elim n0; apply Rle_trans with b; assumption).
  reflexivity.
  elim n; replace a with (Rmin a c).
  elim H0; intros; assumption.
  unfold Rmin in |- *; case (Rle_dec a c); intro;
    [ reflexivity | elim n1; apply Rle_trans with b; assumption ].
  rewrite <- (StepFun_P43 X0 X1 X2).
  apply Rle_lt_trans with
    (Rabs (RiemannInt_SF (mkStepFun X0)) + Rabs (RiemannInt_SF (mkStepFun X1))).
  apply Rabs_triang.
  rewrite (double_var eps);
    replace (RiemannInt_SF (mkStepFun X0)) with (RiemannInt_SF psi1).
  replace (RiemannInt_SF (mkStepFun X1)) with (RiemannInt_SF psi2).
  apply Rplus_lt_compat.
  elim H1; intros; assumption.
  elim H2; intros; assumption.
  apply Rle_antisym.
  apply StepFun_P37; try assumption.
  simpl in |- *; intros; unfold psi3 in |- *; elim H0; clear H0; intros;
    case (Rle_dec a x); case (Rle_dec x b); intros;
      [ elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ r H0))
        | right; reflexivity
        | elim n; apply Rle_trans with b; [ assumption | left; assumption ]
        | elim n0; apply Rle_trans with b; [ assumption | left; assumption ] ].
  apply StepFun_P37; try assumption.
  simpl in |- *; intros; unfold psi3 in |- *; elim H0; clear H0; intros;
    case (Rle_dec a x); case (Rle_dec x b); intros;
      [ elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ r H0))
        | right; reflexivity
        | elim n; apply Rle_trans with b; [ assumption | left; assumption ]
        | elim n0; apply Rle_trans with b; [ assumption | left; assumption ] ].
  apply Rle_antisym.
  apply StepFun_P37; try assumption.
  simpl in |- *; intros; unfold psi3 in |- *; elim H0; clear H0; intros;
    case (Rle_dec a x); case (Rle_dec x b); intros;
      [ right; reflexivity
        | elim n; left; assumption
        | elim n; left; assumption
        | elim n0; left; assumption ].
  apply StepFun_P37; try assumption.
  simpl in |- *; intros; unfold psi3 in |- *; elim H0; clear H0; intros;
    case (Rle_dec a x); case (Rle_dec x b); intros;
      [ right; reflexivity
        | elim n; left; assumption
        | elim n; left; assumption
        | elim n0; left; assumption ].
  apply StepFun_P46 with b; assumption.
  assert (H3 := pre psi2); unfold IsStepFun in H3; unfold is_subdivision in H3;
    elim H3; clear H3; intros l1 [lf1 H3]; split with l1; 
      split with lf1; unfold adapted_couple in H3; decompose [and] H3; 
        clear H3; unfold adapted_couple in |- *; repeat split; 
          try assumption.
  intros; assert (H9 := H8 i H3); unfold constant_D_eq, open_interval in |- *;
    unfold constant_D_eq, open_interval in H9; intros; 
      rewrite <- (H9 x H7); unfold psi3 in |- *; assert (H10 : b < x).
  apply Rle_lt_trans with (pos_Rl l1 i).
  replace b with (Rmin b c).
  rewrite <- H5; elim (RList_P6 l1); intros; apply H10; try assumption.
  apply le_O_n.
  apply lt_trans with (pred (Rlength l1)); try assumption; apply lt_pred_n_n;
    apply neq_O_lt; red in |- *; intro; rewrite <- H12 in H6; 
      discriminate. 
  unfold Rmin in |- *; case (Rle_dec b c); intro;
    [ reflexivity | elim n; assumption ].
  elim H7; intros; assumption.
  case (Rle_dec a x); case (Rle_dec x b); intros;
    [ elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ r H10))
      | reflexivity
      | elim n; apply Rle_trans with b; [ assumption | left; assumption ]
      | elim n0; apply Rle_trans with b; [ assumption | left; assumption ] ].
  assert (H3 := pre psi1); unfold IsStepFun in H3; unfold is_subdivision in H3;
    elim H3; clear H3; intros l1 [lf1 H3]; split with l1; 
      split with lf1; unfold adapted_couple in H3; decompose [and] H3; 
        clear H3; unfold adapted_couple in |- *; repeat split; 
          try assumption.
  intros; assert (H9 := H8 i H3); unfold constant_D_eq, open_interval in |- *;
    unfold constant_D_eq, open_interval in H9; intros; 
      rewrite <- (H9 x H7); unfold psi3 in |- *; assert (H10 : x <= b).
  apply Rle_trans with (pos_Rl l1 (S i)).
  elim H7; intros; left; assumption.
  replace b with (Rmax a b).
  rewrite <- H4; elim (RList_P6 l1); intros; apply H10; try assumption.
  apply lt_pred_n_n; apply neq_O_lt; red in |- *; intro; rewrite <- H12 in H6;
    discriminate. 
  unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; assumption ].
  assert (H11 : a <= x).
  apply Rle_trans with (pos_Rl l1 i).
  replace a with (Rmin a b).
  rewrite <- H5; elim (RList_P6 l1); intros; apply H11; try assumption.
  apply le_O_n.
  apply lt_trans with (pred (Rlength l1)); try assumption; apply lt_pred_n_n;
    apply neq_O_lt; red in |- *; intro; rewrite <- H13 in H6; 
      discriminate. 
  unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; assumption ].
  left; elim H7; intros; assumption.
  case (Rle_dec a x); case (Rle_dec x b); intros; reflexivity || elim n;
    assumption.
  apply StepFun_P46 with b.
  assert (H3 := pre phi1); unfold IsStepFun in H3; unfold is_subdivision in H3;
    elim H3; clear H3; intros l1 [lf1 H3]; split with l1; 
      split with lf1; unfold adapted_couple in H3; decompose [and] H3; 
        clear H3; unfold adapted_couple in |- *; repeat split; 
          try assumption.
  intros; assert (H9 := H8 i H3); unfold constant_D_eq, open_interval in |- *;
    unfold constant_D_eq, open_interval in H9; intros; 
      rewrite <- (H9 x H7); unfold psi3 in |- *; assert (H10 : x <= b).
  apply Rle_trans with (pos_Rl l1 (S i)).
  elim H7; intros; left; assumption.
  replace b with (Rmax a b).
  rewrite <- H4; elim (RList_P6 l1); intros; apply H10; try assumption.
  apply lt_pred_n_n; apply neq_O_lt; red in |- *; intro; rewrite <- H12 in H6;
    discriminate. 
  unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; assumption ].
  assert (H11 : a <= x).
  apply Rle_trans with (pos_Rl l1 i).
  replace a with (Rmin a b).
  rewrite <- H5; elim (RList_P6 l1); intros; apply H11; try assumption.
  apply le_O_n.
  apply lt_trans with (pred (Rlength l1)); try assumption; apply lt_pred_n_n;
    apply neq_O_lt; red in |- *; intro; rewrite <- H13 in H6; 
      discriminate. 
  unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; assumption ].
  left; elim H7; intros; assumption.
  unfold phi3 in |- *; case (Rle_dec a x); case (Rle_dec x b); intros;
    reflexivity || elim n; assumption.
  assert (H3 := pre phi2); unfold IsStepFun in H3; unfold is_subdivision in H3;
    elim H3; clear H3; intros l1 [lf1 H3]; split with l1; 
      split with lf1; unfold adapted_couple in H3; decompose [and] H3; 
        clear H3; unfold adapted_couple in |- *; repeat split; 
          try assumption.
  intros; assert (H9 := H8 i H3); unfold constant_D_eq, open_interval in |- *;
    unfold constant_D_eq, open_interval in H9; intros; 
      rewrite <- (H9 x H7); unfold psi3 in |- *; assert (H10 : b < x).
  apply Rle_lt_trans with (pos_Rl l1 i).
  replace b with (Rmin b c).
  rewrite <- H5; elim (RList_P6 l1); intros; apply H10; try assumption.
  apply le_O_n.
  apply lt_trans with (pred (Rlength l1)); try assumption; apply lt_pred_n_n;
    apply neq_O_lt; red in |- *; intro; rewrite <- H12 in H6; 
      discriminate. 
  unfold Rmin in |- *; case (Rle_dec b c); intro;
    [ reflexivity | elim n; assumption ].
  elim H7; intros; assumption.
  unfold phi3 in |- *; case (Rle_dec a x); case (Rle_dec x b); intros;
    [ elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ r H10))
      | reflexivity
      | elim n; apply Rle_trans with b; [ assumption | left; assumption ]
      | elim n0; apply Rle_trans with b; [ assumption | left; assumption ] ].
Qed.

Lemma RiemannInt_P22 :
  forall (f:R -> R) (a b c:R),
    Riemann_integrable f a b -> a <= c <= b -> Riemann_integrable f a c.
Proof.
  unfold Riemann_integrable in |- *; intros; elim (X eps); clear X;
    intros phi [psi H0]; elim H; elim H0; clear H H0; 
      intros; assert (H3 : IsStepFun phi a c).
  apply StepFun_P44 with b.
  apply (pre phi).
  split; assumption.
  assert (H4 : IsStepFun psi a c).
  apply StepFun_P44 with b.
  apply (pre psi).
  split; assumption.
  split with (mkStepFun H3); split with (mkStepFun H4); split.
  simpl in |- *; intros; apply H.
  replace (Rmin a b) with (Rmin a c).
  elim H5; intros; split; try assumption.
  apply Rle_trans with (Rmax a c); try assumption.
  replace (Rmax a b) with b.
  replace (Rmax a c) with c.
  assumption.
  unfold Rmax in |- *; case (Rle_dec a c); intro;
    [ reflexivity | elim n; assumption ].
  unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; apply Rle_trans with c; assumption ].
  unfold Rmin in |- *; case (Rle_dec a c); case (Rle_dec a b); intros;
    [ reflexivity
      | elim n; apply Rle_trans with c; assumption
      | elim n; assumption
      | elim n0; assumption ].
  rewrite Rabs_right.
  assert (H5 : IsStepFun psi c b).
  apply StepFun_P46 with a.
  apply StepFun_P6; assumption.
  apply (pre psi).
  replace (RiemannInt_SF (mkStepFun H4)) with
  (RiemannInt_SF psi - RiemannInt_SF (mkStepFun H5)).
  apply Rle_lt_trans with (RiemannInt_SF psi).
  unfold Rminus in |- *; pattern (RiemannInt_SF psi) at 2 in |- *;
    rewrite <- Rplus_0_r; apply Rplus_le_compat_l; rewrite <- Ropp_0;
      apply Ropp_ge_le_contravar; apply Rle_ge;
        replace 0 with (RiemannInt_SF (mkStepFun (StepFun_P4 c b 0))).
  apply StepFun_P37; try assumption.
  intros; simpl in |- *; unfold fct_cte in |- *;
    apply Rle_trans with (Rabs (f x - phi x)).
  apply Rabs_pos.
  apply H.
  replace (Rmin a b) with a.
  replace (Rmax a b) with b.
  elim H6; intros; split; left.
  apply Rle_lt_trans with c; assumption.
  assumption.
  unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; apply Rle_trans with c; assumption ].
  unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; apply Rle_trans with c; assumption ].
  rewrite StepFun_P18; ring.
  apply Rle_lt_trans with (Rabs (RiemannInt_SF psi)).
  apply RRle_abs.
  assumption.
  assert (H6 : IsStepFun psi a b).
  apply (pre psi).
  replace (RiemannInt_SF psi) with (RiemannInt_SF (mkStepFun H6)).
  rewrite <- (StepFun_P43 H4 H5 H6); ring.
  unfold RiemannInt_SF in |- *; case (Rle_dec a b); intro.
  eapply StepFun_P17.
  apply StepFun_P1.
  simpl in |- *; apply StepFun_P1.
  apply Ropp_eq_compat; eapply StepFun_P17.
  apply StepFun_P1.
  simpl in |- *; apply StepFun_P1.
  apply Rle_ge; replace 0 with (RiemannInt_SF (mkStepFun (StepFun_P4 a c 0))).
  apply StepFun_P37; try assumption.
  intros; simpl in |- *; unfold fct_cte in |- *;
    apply Rle_trans with (Rabs (f x - phi x)).
  apply Rabs_pos.
  apply H.
  replace (Rmin a b) with a.
  replace (Rmax a b) with b.
  elim H5; intros; split; left.
  assumption.
  apply Rlt_le_trans with c; assumption.
  unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; apply Rle_trans with c; assumption ].
  unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; apply Rle_trans with c; assumption ].
  rewrite StepFun_P18; ring.
Qed.

Lemma RiemannInt_P23 :
  forall (f:R -> R) (a b c:R),
    Riemann_integrable f a b -> a <= c <= b -> Riemann_integrable f c b.
Proof.
  unfold Riemann_integrable in |- *; intros; elim (X eps); clear X;
    intros phi [psi H0]; elim H; elim H0; clear H H0; 
      intros; assert (H3 : IsStepFun phi c b).
  apply StepFun_P45 with a.
  apply (pre phi).
  split; assumption.
  assert (H4 : IsStepFun psi c b).
  apply StepFun_P45 with a.
  apply (pre psi).
  split; assumption.
  split with (mkStepFun H3); split with (mkStepFun H4); split.
  simpl in |- *; intros; apply H.
  replace (Rmax a b) with (Rmax c b).
  elim H5; intros; split; try assumption.
  apply Rle_trans with (Rmin c b); try assumption.
  replace (Rmin a b) with a.
  replace (Rmin c b) with c.
  assumption.
  unfold Rmin in |- *; case (Rle_dec c b); intro;
    [ reflexivity | elim n; assumption ].
  unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; apply Rle_trans with c; assumption ].
  unfold Rmax in |- *; case (Rle_dec c b); case (Rle_dec a b); intros;
    [ reflexivity
      | elim n; apply Rle_trans with c; assumption
      | elim n; assumption
      | elim n0; assumption ].
  rewrite Rabs_right.
  assert (H5 : IsStepFun psi a c).
  apply StepFun_P46 with b.
  apply (pre psi).
  apply StepFun_P6; assumption.
  replace (RiemannInt_SF (mkStepFun H4)) with
  (RiemannInt_SF psi - RiemannInt_SF (mkStepFun H5)).
  apply Rle_lt_trans with (RiemannInt_SF psi).
  unfold Rminus in |- *; pattern (RiemannInt_SF psi) at 2 in |- *;
    rewrite <- Rplus_0_r; apply Rplus_le_compat_l; rewrite <- Ropp_0;
      apply Ropp_ge_le_contravar; apply Rle_ge;
        replace 0 with (RiemannInt_SF (mkStepFun (StepFun_P4 a c 0))).
  apply StepFun_P37; try assumption.
  intros; simpl in |- *; unfold fct_cte in |- *;
    apply Rle_trans with (Rabs (f x - phi x)).
  apply Rabs_pos.
  apply H.
  replace (Rmin a b) with a.
  replace (Rmax a b) with b.
  elim H6; intros; split; left.
  assumption.
  apply Rlt_le_trans with c; assumption.
  unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; apply Rle_trans with c; assumption ].
  unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; apply Rle_trans with c; assumption ].
  rewrite StepFun_P18; ring.
  apply Rle_lt_trans with (Rabs (RiemannInt_SF psi)).
  apply RRle_abs.
  assumption.
  assert (H6 : IsStepFun psi a b).
  apply (pre psi).
  replace (RiemannInt_SF psi) with (RiemannInt_SF (mkStepFun H6)).
  rewrite <- (StepFun_P43 H5 H4 H6); ring.
  unfold RiemannInt_SF in |- *; case (Rle_dec a b); intro.
  eapply StepFun_P17.
  apply StepFun_P1.
  simpl in |- *; apply StepFun_P1.
  apply Ropp_eq_compat; eapply StepFun_P17.
  apply StepFun_P1.
  simpl in |- *; apply StepFun_P1.
  apply Rle_ge; replace 0 with (RiemannInt_SF (mkStepFun (StepFun_P4 c b 0))).
  apply StepFun_P37; try assumption.
  intros; simpl in |- *; unfold fct_cte in |- *;
    apply Rle_trans with (Rabs (f x - phi x)).
  apply Rabs_pos.
  apply H.
  replace (Rmin a b) with a.
  replace (Rmax a b) with b.
  elim H5; intros; split; left.
  apply Rle_lt_trans with c; assumption.
  assumption.
  unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; apply Rle_trans with c; assumption ].
  unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n; apply Rle_trans with c; assumption ].
  rewrite StepFun_P18; ring.
Qed.

Lemma RiemannInt_P24 :
  forall (f:R -> R) (a b c:R),
    Riemann_integrable f a b ->
    Riemann_integrable f b c -> Riemann_integrable f a c.
Proof.
  intros; case (Rle_dec a b); case (Rle_dec b c); intros.
  apply RiemannInt_P21 with b; assumption.
  case (Rle_dec a c); intro.
  apply RiemannInt_P22 with b; try assumption.
  split; [ assumption | auto with real ].
  apply RiemannInt_P1; apply RiemannInt_P22 with b.
  apply RiemannInt_P1; assumption.
  split; auto with real.
  case (Rle_dec a c); intro.
  apply RiemannInt_P23 with b; try assumption.
  split; auto with real.
  apply RiemannInt_P1; apply RiemannInt_P23 with b.
  apply RiemannInt_P1; assumption.
  split; [ assumption | auto with real ].
  apply RiemannInt_P1; apply RiemannInt_P21 with b;
    auto with real || apply RiemannInt_P1; assumption.
Qed.

Lemma RiemannInt_P25 :
  forall (f:R -> R) (a b c:R) (pr1:Riemann_integrable f a b)
    (pr2:Riemann_integrable f b c) (pr3:Riemann_integrable f a c),
    a <= b -> b <= c -> RiemannInt pr1 + RiemannInt pr2 = RiemannInt pr3.
Proof.
  intros f a b c pr1 pr2 pr3 Hyp1 Hyp2; unfold RiemannInt in |- *;
    case (RiemannInt_exists pr1 RinvN RinvN_cv);
    case (RiemannInt_exists pr2 RinvN RinvN_cv);
    case (RiemannInt_exists pr3 RinvN RinvN_cv); intros; 
      symmetry  in |- *; eapply UL_sequence.
  apply u.
  unfold Un_cv in |- *; intros; assert (H0 : 0 < eps / 3).
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ assumption | apply Rinv_0_lt_compat; prove_sup0 ].
  elim (u1 _ H0); clear u1; intros N1 H1; elim (u0 _ H0); clear u0;
    intros N2 H2;
      cut
        (Un_cv
          (fun n:nat =>
            RiemannInt_SF (phi_sequence RinvN pr3 n) -
            (RiemannInt_SF (phi_sequence RinvN pr1 n) +
              RiemannInt_SF (phi_sequence RinvN pr2 n))) 0).
  intro; elim (H3 _ H0); clear H3; intros N3 H3;
    set (N0 := max (max N1 N2) N3); exists N0; intros; 
      unfold R_dist in |- *;
        apply Rle_lt_trans with
          (Rabs
            (RiemannInt_SF (phi_sequence RinvN pr3 n) -
              (RiemannInt_SF (phi_sequence RinvN pr1 n) +
                RiemannInt_SF (phi_sequence RinvN pr2 n))) +
            Rabs
            (RiemannInt_SF (phi_sequence RinvN pr1 n) +
              RiemannInt_SF (phi_sequence RinvN pr2 n) - (x1 + x0))).
  replace (RiemannInt_SF (phi_sequence RinvN pr3 n) - (x1 + x0)) with
  (RiemannInt_SF (phi_sequence RinvN pr3 n) -
    (RiemannInt_SF (phi_sequence RinvN pr1 n) +
      RiemannInt_SF (phi_sequence RinvN pr2 n)) +
    (RiemannInt_SF (phi_sequence RinvN pr1 n) +
      RiemannInt_SF (phi_sequence RinvN pr2 n) - (x1 + x0)));
  [ apply Rabs_triang | ring ].
  replace eps with (eps / 3 + eps / 3 + eps / 3).
  rewrite Rplus_assoc; apply Rplus_lt_compat.
  unfold R_dist in H3; cut (n >= N3)%nat.
  intro; assert (H6 := H3 _ H5); unfold Rminus in H6; rewrite Ropp_0 in H6;
    rewrite Rplus_0_r in H6; apply H6.
  unfold ge in |- *; apply le_trans with N0;
    [ unfold N0 in |- *; apply le_max_r | assumption ].
  apply Rle_lt_trans with
    (Rabs (RiemannInt_SF (phi_sequence RinvN pr1 n) - x1) +
      Rabs (RiemannInt_SF (phi_sequence RinvN pr2 n) - x0)).
  replace
  (RiemannInt_SF (phi_sequence RinvN pr1 n) +
    RiemannInt_SF (phi_sequence RinvN pr2 n) - (x1 + x0)) with
  (RiemannInt_SF (phi_sequence RinvN pr1 n) - x1 +
    (RiemannInt_SF (phi_sequence RinvN pr2 n) - x0));
  [ apply Rabs_triang | ring ].
  apply Rplus_lt_compat.
  unfold R_dist in H1; apply H1.
  unfold ge in |- *; apply le_trans with N0;
    [ apply le_trans with (max N1 N2);
      [ apply le_max_l | unfold N0 in |- *; apply le_max_l ]
      | assumption ].
  unfold R_dist in H2; apply H2.
  unfold ge in |- *; apply le_trans with N0;
    [ apply le_trans with (max N1 N2);
      [ apply le_max_r | unfold N0 in |- *; apply le_max_l ]
      | assumption ].
  apply Rmult_eq_reg_l with 3;
    [ unfold Rdiv in |- *; repeat rewrite Rmult_plus_distr_l;
      do 2 rewrite (Rmult_comm 3); repeat rewrite Rmult_assoc;
        rewrite <- Rinv_l_sym; [ ring | discrR ]
      | discrR ].
  clear x u x0 x1 eps H H0 N1 H1 N2 H2;
    assert
      (H1 :
        exists psi1 : nat -> StepFun a b,
          (forall n:nat,
            (forall t:R,
              Rmin a b <= t /\ t <= Rmax a b ->
              Rabs (f t - phi_sequence RinvN pr1 n t) <= psi1 n t) /\
            Rabs (RiemannInt_SF (psi1 n)) < RinvN n)).
  split with (fun n:nat => projT1 (phi_sequence_prop RinvN pr1 n)); intro;
    apply (projT2 (phi_sequence_prop RinvN pr1 n)). 
  assert
    (H2 :
      exists psi2 : nat -> StepFun b c,
        (forall n:nat,
          (forall t:R,
            Rmin b c <= t /\ t <= Rmax b c ->
            Rabs (f t - phi_sequence RinvN pr2 n t) <= psi2 n t) /\
          Rabs (RiemannInt_SF (psi2 n)) < RinvN n)).
  split with (fun n:nat => projT1 (phi_sequence_prop RinvN pr2 n)); intro;
    apply (projT2 (phi_sequence_prop RinvN pr2 n)). 
  assert
    (H3 :
      exists psi3 : nat -> StepFun a c,
        (forall n:nat,
          (forall t:R,
            Rmin a c <= t /\ t <= Rmax a c ->
            Rabs (f t - phi_sequence RinvN pr3 n t) <= psi3 n t) /\
          Rabs (RiemannInt_SF (psi3 n)) < RinvN n)).
  split with (fun n:nat => projT1 (phi_sequence_prop RinvN pr3 n)); intro;
    apply (projT2 (phi_sequence_prop RinvN pr3 n)). 
  elim H1; clear H1; intros psi1 H1; elim H2; clear H2; intros psi2 H2; elim H3;
    clear H3; intros psi3 H3; assert (H := RinvN_cv); 
      unfold Un_cv in |- *; intros; assert (H4 : 0 < eps / 3).
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ assumption | apply Rinv_0_lt_compat; prove_sup0 ].
  elim (H _ H4); clear H; intros N0 H;
    assert (H5 : forall n:nat, (n >= N0)%nat -> RinvN n < eps / 3).
  intros;
    replace (pos (RinvN n)) with
    (R_dist (mkposreal (/ (INR n + 1)) (RinvN_pos n)) 0).
  apply H; assumption.
  unfold R_dist in |- *; unfold Rminus in |- *; rewrite Ropp_0;
    rewrite Rplus_0_r; apply Rabs_right; apply Rle_ge; 
      left; apply (cond_pos (RinvN n)).
  exists N0; intros; elim (H1 n); elim (H2 n); elim (H3 n); clear H1 H2 H3;
    intros; unfold R_dist in |- *; unfold Rminus in |- *; 
      rewrite Ropp_0; rewrite Rplus_0_r; 
        set (phi1 := phi_sequence RinvN pr1 n) in H8 |- *;
          set (phi2 := phi_sequence RinvN pr2 n) in H3 |- *; 
            set (phi3 := phi_sequence RinvN pr3 n) in H1 |- *; 
              assert (H10 : IsStepFun phi3 a b).
  apply StepFun_P44 with c.
  apply (pre phi3).
  split; assumption.
  assert (H11 : IsStepFun (psi3 n) a b).
  apply StepFun_P44 with c.
  apply (pre (psi3 n)).
  split; assumption.
  assert (H12 : IsStepFun phi3 b c).
  apply StepFun_P45 with a.
  apply (pre phi3).
  split; assumption.
  assert (H13 : IsStepFun (psi3 n) b c).
  apply StepFun_P45 with a.
  apply (pre (psi3 n)).
  split; assumption.
  replace (RiemannInt_SF phi3) with
  (RiemannInt_SF (mkStepFun H10) + RiemannInt_SF (mkStepFun H12)).
  apply Rle_lt_trans with
    (Rabs (RiemannInt_SF (mkStepFun H10) - RiemannInt_SF phi1) +
      Rabs (RiemannInt_SF (mkStepFun H12) - RiemannInt_SF phi2)).
  replace
  (RiemannInt_SF (mkStepFun H10) + RiemannInt_SF (mkStepFun H12) +
    - (RiemannInt_SF phi1 + RiemannInt_SF phi2)) with
  (RiemannInt_SF (mkStepFun H10) - RiemannInt_SF phi1 +
    (RiemannInt_SF (mkStepFun H12) - RiemannInt_SF phi2));
  [ apply Rabs_triang | ring ].
  replace (RiemannInt_SF (mkStepFun H10) - RiemannInt_SF phi1) with
  (RiemannInt_SF (mkStepFun (StepFun_P28 (-1) (mkStepFun H10) phi1))).
  replace (RiemannInt_SF (mkStepFun H12) - RiemannInt_SF phi2) with
  (RiemannInt_SF (mkStepFun (StepFun_P28 (-1) (mkStepFun H12) phi2))).
  apply Rle_lt_trans with
    (RiemannInt_SF
      (mkStepFun
        (StepFun_P32 (mkStepFun (StepFun_P28 (-1) (mkStepFun H10) phi1)))) +
      RiemannInt_SF
      (mkStepFun
        (StepFun_P32 (mkStepFun (StepFun_P28 (-1) (mkStepFun H12) phi2))))).
  apply Rle_trans with
    (Rabs (RiemannInt_SF (mkStepFun (StepFun_P28 (-1) (mkStepFun H10) phi1))) +
      RiemannInt_SF
      (mkStepFun
        (StepFun_P32 (mkStepFun (StepFun_P28 (-1) (mkStepFun H12) phi2))))).
  apply Rplus_le_compat_l.
  apply StepFun_P34; try assumption.
  do 2
    rewrite <-
      (Rplus_comm
        (RiemannInt_SF
          (mkStepFun
            (StepFun_P32 (mkStepFun (StepFun_P28 (-1) (mkStepFun H12) phi2))))))
      ; apply Rplus_le_compat_l; apply StepFun_P34; try assumption.
  apply Rle_lt_trans with
    (RiemannInt_SF (mkStepFun (StepFun_P28 1 (mkStepFun H11) (psi1 n))) +
      RiemannInt_SF (mkStepFun (StepFun_P28 1 (mkStepFun H13) (psi2 n)))).
  apply Rle_trans with
    (RiemannInt_SF
      (mkStepFun
        (StepFun_P32 (mkStepFun (StepFun_P28 (-1) (mkStepFun H10) phi1)))) +
      RiemannInt_SF (mkStepFun (StepFun_P28 1 (mkStepFun H13) (psi2 n)))).
  apply Rplus_le_compat_l; apply StepFun_P37; try assumption.
  intros; simpl in |- *; rewrite Rmult_1_l;
    apply Rle_trans with (Rabs (f x - phi3 x) + Rabs (f x - phi2 x)).
  rewrite <- (Rabs_Ropp (f x - phi3 x)); rewrite Ropp_minus_distr;
    replace (phi3 x + -1 * phi2 x) with (phi3 x - f x + (f x - phi2 x));
    [ apply Rabs_triang | ring ].
  apply Rplus_le_compat.
  apply H1.
  elim H14; intros; split.
  replace (Rmin a c) with a.
  apply Rle_trans with b; try assumption.
  left; assumption.
  unfold Rmin in |- *; case (Rle_dec a c); intro;
    [ reflexivity | elim n0; apply Rle_trans with b; assumption ].
  replace (Rmax a c) with c.
  left; assumption.
  unfold Rmax in |- *; case (Rle_dec a c); intro;
    [ reflexivity | elim n0; apply Rle_trans with b; assumption ].
  apply H3.
  elim H14; intros; split.
  replace (Rmin b c) with b.
  left; assumption.
  unfold Rmin in |- *; case (Rle_dec b c); intro;
    [ reflexivity | elim n0; assumption ].
  replace (Rmax b c) with c.
  left; assumption.
  unfold Rmax in |- *; case (Rle_dec b c); intro;
    [ reflexivity | elim n0; assumption ].
  do 2
    rewrite <-
      (Rplus_comm
        (RiemannInt_SF (mkStepFun (StepFun_P28 1 (mkStepFun H13) (psi2 n)))))
      ; apply Rplus_le_compat_l; apply StepFun_P37; try assumption.
  intros; simpl in |- *; rewrite Rmult_1_l;
    apply Rle_trans with (Rabs (f x - phi3 x) + Rabs (f x - phi1 x)).
  rewrite <- (Rabs_Ropp (f x - phi3 x)); rewrite Ropp_minus_distr;
    replace (phi3 x + -1 * phi1 x) with (phi3 x - f x + (f x - phi1 x));
    [ apply Rabs_triang | ring ].
  apply Rplus_le_compat.
  apply H1.
  elim H14; intros; split.
  replace (Rmin a c) with a.
  left; assumption.
  unfold Rmin in |- *; case (Rle_dec a c); intro;
    [ reflexivity | elim n0; apply Rle_trans with b; assumption ].
  replace (Rmax a c) with c.
  apply Rle_trans with b.
  left; assumption.
  assumption.
  unfold Rmax in |- *; case (Rle_dec a c); intro;
    [ reflexivity | elim n0; apply Rle_trans with b; assumption ].
  apply H8.
  elim H14; intros; split.
  replace (Rmin a b) with a.
  left; assumption.
  unfold Rmin in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n0; assumption ].
  replace (Rmax a b) with b.
  left; assumption.
  unfold Rmax in |- *; case (Rle_dec a b); intro;
    [ reflexivity | elim n0; assumption ].
  do 2 rewrite StepFun_P30.
  do 2 rewrite Rmult_1_l;
    replace
    (RiemannInt_SF (mkStepFun H11) + RiemannInt_SF (psi1 n) +
      (RiemannInt_SF (mkStepFun H13) + RiemannInt_SF (psi2 n))) with
    (RiemannInt_SF (psi3 n) + RiemannInt_SF (psi1 n) + RiemannInt_SF (psi2 n)).
  replace eps with (eps / 3 + eps / 3 + eps / 3).
  repeat rewrite Rplus_assoc; repeat apply Rplus_lt_compat.
  apply Rle_lt_trans with (Rabs (RiemannInt_SF (psi3 n))).
  apply RRle_abs.
  apply Rlt_trans with (pos (RinvN n)).
  assumption.
  apply H5; assumption.
  apply Rle_lt_trans with (Rabs (RiemannInt_SF (psi1 n))).
  apply RRle_abs.
  apply Rlt_trans with (pos (RinvN n)).
  assumption.
  apply H5; assumption.
  apply Rle_lt_trans with (Rabs (RiemannInt_SF (psi2 n))).
  apply RRle_abs.
  apply Rlt_trans with (pos (RinvN n)).
  assumption.
  apply H5; assumption.
  apply Rmult_eq_reg_l with 3;
    [ unfold Rdiv in |- *; repeat rewrite Rmult_plus_distr_l;
      do 2 rewrite (Rmult_comm 3); repeat rewrite Rmult_assoc;
        rewrite <- Rinv_l_sym; [ ring | discrR ]
      | discrR ].
  replace (RiemannInt_SF (psi3 n)) with
  (RiemannInt_SF (mkStepFun (pre (psi3 n)))).
  rewrite <- (StepFun_P43 H11 H13 (pre (psi3 n))); ring.
  reflexivity.
  rewrite StepFun_P30; ring.
  rewrite StepFun_P30; ring.
  apply (StepFun_P43 H10 H12 (pre phi3)).
Qed.

Lemma RiemannInt_P26 :
  forall (f:R -> R) (a b c:R) (pr1:Riemann_integrable f a b)
    (pr2:Riemann_integrable f b c) (pr3:Riemann_integrable f a c),
    RiemannInt pr1 + RiemannInt pr2 = RiemannInt pr3.
Proof.
  intros; case (Rle_dec a b); case (Rle_dec b c); intros.
  apply RiemannInt_P25; assumption.
  case (Rle_dec a c); intro.
  assert (H : c <= b).
  auto with real.
  rewrite <- (RiemannInt_P25 pr3 (RiemannInt_P1 pr2) pr1 r0 H);
    rewrite (RiemannInt_P8 pr2 (RiemannInt_P1 pr2)); ring.
  assert (H : c <= a).
  auto with real.
  rewrite (RiemannInt_P8 pr2 (RiemannInt_P1 pr2));
    rewrite <- (RiemannInt_P25 (RiemannInt_P1 pr3) pr1 (RiemannInt_P1 pr2) H r);
      rewrite (RiemannInt_P8 pr3 (RiemannInt_P1 pr3)); ring.
  assert (H : b <= a).
  auto with real.
  case (Rle_dec a c); intro.
  rewrite <- (RiemannInt_P25 (RiemannInt_P1 pr1) pr3 pr2 H r0);
    rewrite (RiemannInt_P8 pr1 (RiemannInt_P1 pr1)); ring.
  assert (H0 : c <= a).
  auto with real.
  rewrite (RiemannInt_P8 pr1 (RiemannInt_P1 pr1));
    rewrite <- (RiemannInt_P25 pr2 (RiemannInt_P1 pr3) (RiemannInt_P1 pr1) r H0);
      rewrite (RiemannInt_P8 pr3 (RiemannInt_P1 pr3)); ring.
  rewrite (RiemannInt_P8 pr1 (RiemannInt_P1 pr1));
    rewrite (RiemannInt_P8 pr2 (RiemannInt_P1 pr2));
      rewrite (RiemannInt_P8 pr3 (RiemannInt_P1 pr3));
        rewrite <-
          (RiemannInt_P25 (RiemannInt_P1 pr2) (RiemannInt_P1 pr1) (RiemannInt_P1 pr3))
          ; [ ring | auto with real | auto with real ].
Qed.

Lemma RiemannInt_P27 :
  forall (f:R -> R) (a b x:R) (h:a <= b)
    (C0:forall x:R, a <= x <= b -> continuity_pt f x),
    a < x < b -> derivable_pt_lim (primitive h (FTC_P1 h C0)) x (f x).
Proof.
  intro f; intros; elim H; clear H; intros; assert (H1 : continuity_pt f x).
  apply C0; split; left; assumption.
  unfold derivable_pt_lim in |- *; intros; assert (Hyp : 0 < eps / 2).
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ assumption | apply Rinv_0_lt_compat; prove_sup0 ].
  elim (H1 _ Hyp); unfold dist, D_x, no_cond in |- *; simpl in |- *;
    unfold R_dist in |- *; intros; set (del := Rmin x0 (Rmin (b - x) (x - a)));
      assert (H4 : 0 < del).
  unfold del in |- *; unfold Rmin in |- *; case (Rle_dec (b - x) (x - a));
    intro.
  case (Rle_dec x0 (b - x)); intro;
    [ elim H3; intros; assumption | apply Rlt_Rminus; assumption ].
  case (Rle_dec x0 (x - a)); intro;
    [ elim H3; intros; assumption | apply Rlt_Rminus; assumption ].
  split with (mkposreal _ H4); intros;
    assert (H7 : Riemann_integrable f x (x + h0)).
  case (Rle_dec x (x + h0)); intro.
  apply continuity_implies_RiemannInt; try assumption.
  intros; apply C0; elim H7; intros; split.
  apply Rle_trans with x; [ left; assumption | assumption ].
  apply Rle_trans with (x + h0).
  assumption.
  left; apply Rlt_le_trans with (x + del).
  apply Rplus_lt_compat_l; apply Rle_lt_trans with (Rabs h0);
    [ apply RRle_abs | apply H6 ].
  unfold del in |- *; apply Rle_trans with (x + Rmin (b - x) (x - a)).
  apply Rplus_le_compat_l; apply Rmin_r.
  pattern b at 2 in |- *; replace b with (x + (b - x));
    [ apply Rplus_le_compat_l; apply Rmin_l | ring ].
  apply RiemannInt_P1; apply continuity_implies_RiemannInt; auto with real.
  intros; apply C0; elim H7; intros; split.
  apply Rle_trans with (x + h0).
  left; apply Rle_lt_trans with (x - del).
  unfold del in |- *; apply Rle_trans with (x - Rmin (b - x) (x - a)).
  pattern a at 1 in |- *; replace a with (x + (a - x)); [ idtac | ring ].
  unfold Rminus in |- *; apply Rplus_le_compat_l; apply Ropp_le_cancel.
  rewrite Ropp_involutive; rewrite Ropp_plus_distr; rewrite Ropp_involutive;
    rewrite (Rplus_comm x); apply Rmin_r.
  unfold Rminus in |- *; apply Rplus_le_compat_l; apply Ropp_le_cancel.
  do 2 rewrite Ropp_involutive; apply Rmin_r.
  unfold Rminus in |- *; apply Rplus_lt_compat_l; apply Ropp_lt_cancel.
  rewrite Ropp_involutive; apply Rle_lt_trans with (Rabs h0);
    [ rewrite <- Rabs_Ropp; apply RRle_abs | apply H6 ].
  assumption.
  apply Rle_trans with x; [ assumption | left; assumption ].
  replace (primitive h (FTC_P1 h C0) (x + h0) - primitive h (FTC_P1 h C0) x)
    with (RiemannInt H7).
  replace (f x) with (RiemannInt (RiemannInt_P14 x (x + h0) (f x)) / h0).
  replace
  (RiemannInt H7 / h0 - RiemannInt (RiemannInt_P14 x (x + h0) (f x)) / h0)
    with ((RiemannInt H7 - RiemannInt (RiemannInt_P14 x (x + h0) (f x))) / h0).
  replace (RiemannInt H7 - RiemannInt (RiemannInt_P14 x (x + h0) (f x))) with
  (RiemannInt (RiemannInt_P10 (-1) H7 (RiemannInt_P14 x (x + h0) (f x)))).
  unfold Rdiv in |- *; rewrite Rabs_mult; case (Rle_dec x (x + h0)); intro.
  apply Rle_lt_trans with
    (RiemannInt
      (RiemannInt_P16
        (RiemannInt_P10 (-1) H7 (RiemannInt_P14 x (x + h0) (f x)))) *
      Rabs (/ h0)).
  do 2 rewrite <- (Rmult_comm (Rabs (/ h0))); apply Rmult_le_compat_l.
  apply Rabs_pos.
  apply
    (RiemannInt_P17 (RiemannInt_P10 (-1) H7 (RiemannInt_P14 x (x + h0) (f x)))
      (RiemannInt_P16
        (RiemannInt_P10 (-1) H7 (RiemannInt_P14 x (x + h0) (f x)))));
    assumption.
  apply Rle_lt_trans with
    (RiemannInt (RiemannInt_P14 x (x + h0) (eps / 2)) * Rabs (/ h0)).
  do 2 rewrite <- (Rmult_comm (Rabs (/ h0))); apply Rmult_le_compat_l.
  apply Rabs_pos.
  apply RiemannInt_P19; try assumption.
  intros; replace (f x1 + -1 * fct_cte (f x) x1) with (f x1 - f x).
  unfold fct_cte in |- *; case (Req_dec x x1); intro.
  rewrite H9; unfold Rminus in |- *; rewrite Rplus_opp_r; rewrite Rabs_R0; left;
    assumption.
  elim H3; intros; left; apply H11.
  repeat split.
  assumption.
  rewrite Rabs_right.
  apply Rplus_lt_reg_r with x; replace (x + (x1 - x)) with x1; [ idtac | ring ].
  apply Rlt_le_trans with (x + h0).
  elim H8; intros; assumption.
  apply Rplus_le_compat_l; apply Rle_trans with del.
  left; apply Rle_lt_trans with (Rabs h0); [ apply RRle_abs | assumption ].
  unfold del in |- *; apply Rmin_l.
  apply Rge_minus; apply Rle_ge; left; elim H8; intros; assumption.
  unfold fct_cte in |- *; ring.
  rewrite RiemannInt_P15.
  rewrite Rmult_assoc; replace ((x + h0 - x) * Rabs (/ h0)) with 1.
  rewrite Rmult_1_r; unfold Rdiv in |- *; apply Rmult_lt_reg_l with 2;
    [ prove_sup0
      | rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
        rewrite <- Rinv_r_sym;
          [ rewrite Rmult_1_l; pattern eps at 1 in |- *; rewrite <- Rplus_0_r;
            rewrite double; apply Rplus_lt_compat_l; assumption
            | discrR ] ].
  rewrite Rabs_right.
  replace (x + h0 - x) with h0; [ idtac | ring ].
  apply Rinv_r_sym.
  assumption.
  apply Rle_ge; left; apply Rinv_0_lt_compat.
  elim r; intro.
  apply Rplus_lt_reg_r with x; rewrite Rplus_0_r; assumption.
  elim H5; symmetry  in |- *; apply Rplus_eq_reg_l with x; rewrite Rplus_0_r;
    assumption.
  apply Rle_lt_trans with
    (RiemannInt
      (RiemannInt_P16
        (RiemannInt_P1
          (RiemannInt_P10 (-1) H7 (RiemannInt_P14 x (x + h0) (f x))))) *
      Rabs (/ h0)).
  do 2 rewrite <- (Rmult_comm (Rabs (/ h0))); apply Rmult_le_compat_l.
  apply Rabs_pos.
  replace
  (RiemannInt (RiemannInt_P10 (-1) H7 (RiemannInt_P14 x (x + h0) (f x)))) with
  (-
    RiemannInt
    (RiemannInt_P1 (RiemannInt_P10 (-1) H7 (RiemannInt_P14 x (x + h0) (f x))))).
  rewrite Rabs_Ropp;
    apply
      (RiemannInt_P17
        (RiemannInt_P1
          (RiemannInt_P10 (-1) H7 (RiemannInt_P14 x (x + h0) (f x))))
        (RiemannInt_P16
          (RiemannInt_P1
            (RiemannInt_P10 (-1) H7 (RiemannInt_P14 x (x + h0) (f x))))));
      auto with real.
  symmetry  in |- *; apply RiemannInt_P8.
  apply Rle_lt_trans with
    (RiemannInt (RiemannInt_P14 (x + h0) x (eps / 2)) * Rabs (/ h0)).
  do 2 rewrite <- (Rmult_comm (Rabs (/ h0))); apply Rmult_le_compat_l.
  apply Rabs_pos.
  apply RiemannInt_P19.
  auto with real.
  intros; replace (f x1 + -1 * fct_cte (f x) x1) with (f x1 - f x).
  unfold fct_cte in |- *; case (Req_dec x x1); intro.
  rewrite H9; unfold Rminus in |- *; rewrite Rplus_opp_r; rewrite Rabs_R0; left;
    assumption.
  elim H3; intros; left; apply H11.
  repeat split.
  assumption.
  rewrite Rabs_left.
  apply Rplus_lt_reg_r with (x1 - x0); replace (x1 - x0 + x0) with x1;
    [ idtac | ring ].
  replace (x1 - x0 + - (x1 - x)) with (x - x0); [ idtac | ring ].
  apply Rle_lt_trans with (x + h0).
  unfold Rminus in |- *; apply Rplus_le_compat_l; apply Ropp_le_cancel.
  rewrite Ropp_involutive; apply Rle_trans with (Rabs h0).
  rewrite <- Rabs_Ropp; apply RRle_abs.
  apply Rle_trans with del;
    [ left; assumption | unfold del in |- *; apply Rmin_l ].
  elim H8; intros; assumption.
  apply Rplus_lt_reg_r with x; rewrite Rplus_0_r;
    replace (x + (x1 - x)) with x1; [ elim H8; intros; assumption | ring ].
  unfold fct_cte in |- *; ring.
  rewrite RiemannInt_P15.
  rewrite Rmult_assoc; replace ((x - (x + h0)) * Rabs (/ h0)) with 1.
  rewrite Rmult_1_r; unfold Rdiv in |- *; apply Rmult_lt_reg_l with 2;
    [ prove_sup0
      | rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
        rewrite <- Rinv_r_sym;
          [ rewrite Rmult_1_l; pattern eps at 1 in |- *; rewrite <- Rplus_0_r;
            rewrite double; apply Rplus_lt_compat_l; assumption
            | discrR ] ].
  rewrite Rabs_left.
  replace (x - (x + h0)) with (- h0); [ idtac | ring ].
  rewrite Ropp_mult_distr_l_reverse; rewrite Ropp_mult_distr_r_reverse;
    rewrite Ropp_involutive; apply Rinv_r_sym.
  assumption.
  apply Rinv_lt_0_compat.
  assert (H8 : x + h0 < x).
  auto with real.
  apply Rplus_lt_reg_r with x; rewrite Rplus_0_r; assumption.
  rewrite
    (RiemannInt_P13 H7 (RiemannInt_P14 x (x + h0) (f x))
      (RiemannInt_P10 (-1) H7 (RiemannInt_P14 x (x + h0) (f x))))
    .
  ring.
  unfold Rdiv, Rminus in |- *; rewrite Rmult_plus_distr_r; ring.
  rewrite RiemannInt_P15; apply Rmult_eq_reg_l with h0;
    [ unfold Rdiv in |- *; rewrite (Rmult_comm h0); repeat rewrite Rmult_assoc;
      rewrite <- Rinv_l_sym; [ ring | assumption ]
      | assumption ].
  cut (a <= x + h0).
  cut (x + h0 <= b).
  intros; unfold primitive in |- *.
  case (Rle_dec a (x + h0)); case (Rle_dec (x + h0) b); case (Rle_dec a x);
  case (Rle_dec x b); intros; try (elim n; assumption || left; assumption).
  rewrite <- (RiemannInt_P26 (FTC_P1 h C0 r0 r) H7 (FTC_P1 h C0 r2 r1)); ring.
  apply Rplus_le_reg_l with (- x); replace (- x + (x + h0)) with h0;
    [ idtac | ring ].
  rewrite Rplus_comm; apply Rle_trans with (Rabs h0).
  apply RRle_abs.
  apply Rle_trans with del;
    [ left; assumption
      | unfold del in |- *; apply Rle_trans with (Rmin (b - x) (x - a));
        [ apply Rmin_r | apply Rmin_l ] ].
  apply Ropp_le_cancel; apply Rplus_le_reg_l with x;
    replace (x + - (x + h0)) with (- h0); [ idtac | ring ].
  apply Rle_trans with (Rabs h0);
    [ rewrite <- Rabs_Ropp; apply RRle_abs
      | apply Rle_trans with del;
        [ left; assumption
          | unfold del in |- *; apply Rle_trans with (Rmin (b - x) (x - a));
            apply Rmin_r ] ].
Qed.

Lemma RiemannInt_P28 :
  forall (f:R -> R) (a b x:R) (h:a <= b)
    (C0:forall x:R, a <= x <= b -> continuity_pt f x),
    a <= x <= b -> derivable_pt_lim (primitive h (FTC_P1 h C0)) x (f x).
Proof.
  intro f; intros; elim h; intro.
  elim H; clear H; intros; elim H; intro.
  elim H1; intro.
  apply RiemannInt_P27; split; assumption.
  set
    (f_b := fun x:R => f b * (x - b) + RiemannInt (FTC_P1 h C0 h (Rle_refl b)));
    rewrite H3.
  assert (H4 : derivable_pt_lim f_b b (f b)).
  unfold f_b in |- *; pattern (f b) at 2 in |- *; replace (f b) with (f b + 0).
  change
    (derivable_pt_lim
      ((fct_cte (f b) * (id - fct_cte b))%F +
        fct_cte (RiemannInt (FTC_P1 h C0 h (Rle_refl b)))) b (
          f b + 0)) in |- *. 
  apply derivable_pt_lim_plus.
  pattern (f b) at 2 in |- *;
    replace (f b) with (0 * (id - fct_cte b)%F b + fct_cte (f b) b * 1).
  apply derivable_pt_lim_mult.
  apply derivable_pt_lim_const.
  replace 1 with (1 - 0); [ idtac | ring ].
  apply derivable_pt_lim_minus.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
  unfold fct_cte in |- *; ring.
  apply derivable_pt_lim_const.
  ring.
  unfold derivable_pt_lim in |- *; intros; elim (H4 _ H5); intros;
    assert (H7 : continuity_pt f b).
  apply C0; split; [ left; assumption | right; reflexivity ].
  assert (H8 : 0 < eps / 2).
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ assumption | apply Rinv_0_lt_compat; prove_sup0 ].
  elim (H7 _ H8); unfold D_x, no_cond, dist in |- *; simpl in |- *;
    unfold R_dist in |- *; intros; set (del := Rmin x0 (Rmin x1 (b - a)));
      assert (H10 : 0 < del).
  unfold del in |- *; unfold Rmin in |- *; case (Rle_dec x1 (b - a)); intros.
  case (Rle_dec x0 x1); intro;
    [ apply (cond_pos x0) | elim H9; intros; assumption ].
  case (Rle_dec x0 (b - a)); intro;
    [ apply (cond_pos x0) | apply Rlt_Rminus; assumption ].
  split with (mkposreal _ H10); intros; case (Rcase_abs h0); intro.
  assert (H14 : b + h0 < b).
  pattern b at 2 in |- *; rewrite <- Rplus_0_r; apply Rplus_lt_compat_l;
    assumption.
  assert (H13 : Riemann_integrable f (b + h0) b).
  apply continuity_implies_RiemannInt.
  left; assumption.
  intros; apply C0; elim H13; intros; split; try assumption.
  apply Rle_trans with (b + h0); try assumption.
  apply Rplus_le_reg_l with (- a - h0).
  replace (- a - h0 + a) with (- h0); [ idtac | ring ].
  replace (- a - h0 + (b + h0)) with (b - a); [ idtac | ring ].
  apply Rle_trans with del.
  apply Rle_trans with (Rabs h0).
  rewrite <- Rabs_Ropp; apply RRle_abs.
  left; assumption.
  unfold del in |- *; apply Rle_trans with (Rmin x1 (b - a)); apply Rmin_r.
  replace (primitive h (FTC_P1 h C0) (b + h0) - primitive h (FTC_P1 h C0) b)
    with (- RiemannInt H13).
  replace (f b) with (- RiemannInt (RiemannInt_P14 (b + h0) b (f b)) / h0).
  rewrite <- Rabs_Ropp; unfold Rminus in |- *; unfold Rdiv in |- *;
    rewrite Ropp_mult_distr_l_reverse; rewrite Ropp_plus_distr;
      repeat rewrite Ropp_involutive;
        replace
        (RiemannInt H13 * / h0 +
          - RiemannInt (RiemannInt_P14 (b + h0) b (f b)) * / h0) with
        ((RiemannInt H13 - RiemannInt (RiemannInt_P14 (b + h0) b (f b))) / h0).
  replace (RiemannInt H13 - RiemannInt (RiemannInt_P14 (b + h0) b (f b))) with
  (RiemannInt (RiemannInt_P10 (-1) H13 (RiemannInt_P14 (b + h0) b (f b)))).
  unfold Rdiv in |- *; rewrite Rabs_mult;
    apply Rle_lt_trans with
      (RiemannInt
        (RiemannInt_P16
          (RiemannInt_P10 (-1) H13 (RiemannInt_P14 (b + h0) b (f b)))) *
        Rabs (/ h0)).
  do 2 rewrite <- (Rmult_comm (Rabs (/ h0))); apply Rmult_le_compat_l.
  apply Rabs_pos.
  apply
    (RiemannInt_P17 (RiemannInt_P10 (-1) H13 (RiemannInt_P14 (b + h0) b (f b)))
      (RiemannInt_P16
        (RiemannInt_P10 (-1) H13 (RiemannInt_P14 (b + h0) b (f b))))); 
    left; assumption.
  apply Rle_lt_trans with
    (RiemannInt (RiemannInt_P14 (b + h0) b (eps / 2)) * Rabs (/ h0)).
  do 2 rewrite <- (Rmult_comm (Rabs (/ h0))); apply Rmult_le_compat_l.
  apply Rabs_pos.
  apply RiemannInt_P19.
  left; assumption.
  intros; replace (f x2 + -1 * fct_cte (f b) x2) with (f x2 - f b).
  unfold fct_cte in |- *; case (Req_dec b x2); intro.
  rewrite H16; unfold Rminus in |- *; rewrite Rplus_opp_r; rewrite Rabs_R0;
    left; assumption.
  elim H9; intros; left; apply H18.
  repeat split.
  assumption.
  rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr; rewrite Rabs_right.
  apply Rplus_lt_reg_r with (x2 - x1);
    replace (x2 - x1 + (b - x2)) with (b - x1); [ idtac | ring ].
  replace (x2 - x1 + x1) with x2; [ idtac | ring ].
  apply Rlt_le_trans with (b + h0).
  2: elim H15; intros; left; assumption.
  unfold Rminus in |- *; apply Rplus_lt_compat_l; apply Ropp_lt_cancel;
    rewrite Ropp_involutive; apply Rle_lt_trans with (Rabs h0).
  rewrite <- Rabs_Ropp; apply RRle_abs.
  apply Rlt_le_trans with del;
    [ assumption
      | unfold del in |- *; apply Rle_trans with (Rmin x1 (b - a));
        [ apply Rmin_r | apply Rmin_l ] ].
  apply Rle_ge; left; apply Rlt_Rminus; elim H15; intros; assumption.
  unfold fct_cte in |- *; ring.
  rewrite RiemannInt_P15.
  rewrite Rmult_assoc; replace ((b - (b + h0)) * Rabs (/ h0)) with 1.
  rewrite Rmult_1_r; unfold Rdiv in |- *; apply Rmult_lt_reg_l with 2;
    [ prove_sup0
      | rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
        rewrite <- Rinv_r_sym;
          [ rewrite Rmult_1_l; pattern eps at 1 in |- *; rewrite <- Rplus_0_r;
            rewrite double; apply Rplus_lt_compat_l; assumption
            | discrR ] ].
  rewrite Rabs_left.
  apply Rmult_eq_reg_l with h0;
    [ do 2 rewrite (Rmult_comm h0); rewrite Rmult_assoc;
      rewrite Ropp_mult_distr_l_reverse; rewrite <- Rinv_l_sym;
        [ ring | assumption ]
      | assumption ].
  apply Rinv_lt_0_compat; assumption.
  rewrite
    (RiemannInt_P13 H13 (RiemannInt_P14 (b + h0) b (f b))
      (RiemannInt_P10 (-1) H13 (RiemannInt_P14 (b + h0) b (f b))))
    ; ring.
  unfold Rdiv, Rminus in |- *; rewrite Rmult_plus_distr_r; ring.
  rewrite RiemannInt_P15.
  rewrite <- Ropp_mult_distr_l_reverse; apply Rmult_eq_reg_l with h0;
    [ repeat rewrite (Rmult_comm h0); unfold Rdiv in |- *;
      repeat rewrite Rmult_assoc; rewrite <- Rinv_l_sym; 
        [ ring | assumption ]
      | assumption ].
  cut (a <= b + h0).
  cut (b + h0 <= b).
  intros; unfold primitive in |- *; case (Rle_dec a (b + h0));
    case (Rle_dec (b + h0) b); case (Rle_dec a b); case (Rle_dec b b); 
    intros; try (elim n; right; reflexivity) || (elim n; left; assumption).
  rewrite <- (RiemannInt_P26 (FTC_P1 h C0 r3 r2) H13 (FTC_P1 h C0 r1 r0)); ring.
  elim n; assumption.
  left; assumption.
  apply Rplus_le_reg_l with (- a - h0).
  replace (- a - h0 + a) with (- h0); [ idtac | ring ].
  replace (- a - h0 + (b + h0)) with (b - a); [ idtac | ring ].
  apply Rle_trans with del.
  apply Rle_trans with (Rabs h0).
  rewrite <- Rabs_Ropp; apply RRle_abs.
  left; assumption.
  unfold del in |- *; apply Rle_trans with (Rmin x1 (b - a)); apply Rmin_r.
  cut (primitive h (FTC_P1 h C0) b = f_b b).
  intro; cut (primitive h (FTC_P1 h C0) (b + h0) = f_b (b + h0)).
  intro; rewrite H13; rewrite H14; apply H6.
  assumption.
  apply Rlt_le_trans with del;
    [ assumption | unfold del in |- *; apply Rmin_l ].
  assert (H14 : b < b + h0).
  pattern b at 1 in |- *; rewrite <- Rplus_0_r; apply Rplus_lt_compat_l.
  assert (H14 := Rge_le _ _ r); elim H14; intro.
  assumption.
  elim H11; symmetry  in |- *; assumption.
  unfold primitive in |- *; case (Rle_dec a (b + h0));
    case (Rle_dec (b + h0) b); intros;
      [ elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ r0 H14))
        | unfold f_b in |- *; reflexivity
        | elim n; left; apply Rlt_trans with b; assumption
        | elim n0; left; apply Rlt_trans with b; assumption ].
  unfold f_b in |- *; unfold Rminus in |- *; rewrite Rplus_opp_r;
    rewrite Rmult_0_r; rewrite Rplus_0_l; unfold primitive in |- *;
      case (Rle_dec a b); case (Rle_dec b b); intros;
        [ apply RiemannInt_P5
          | elim n; right; reflexivity
          | elim n; left; assumption
          | elim n; right; reflexivity ].
(*****)
  set (f_a := fun x:R => f a * (x - a)); rewrite <- H2;
    assert (H3 : derivable_pt_lim f_a a (f a)).
  unfold f_a in |- *;
    change (derivable_pt_lim (fct_cte (f a) * (id - fct_cte a)%F) a (f a))
      in |- *; pattern (f a) at 2 in |- *;
        replace (f a) with (0 * (id - fct_cte a)%F a + fct_cte (f a) a * 1).
  apply derivable_pt_lim_mult.
  apply derivable_pt_lim_const.
  replace 1 with (1 - 0); [ idtac | ring ].
  apply derivable_pt_lim_minus.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
  unfold fct_cte in |- *; ring.
  unfold derivable_pt_lim in |- *; intros; elim (H3 _ H4); intros.
  assert (H6 : continuity_pt f a).
  apply C0; split; [ right; reflexivity | left; assumption ].
  assert (H7 : 0 < eps / 2).
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ assumption | apply Rinv_0_lt_compat; prove_sup0 ].
  elim (H6 _ H7); unfold D_x, no_cond, dist in |- *; simpl in |- *;
    unfold R_dist in |- *; intros.
  set (del := Rmin x0 (Rmin x1 (b - a))).
  assert (H9 : 0 < del).
  unfold del in |- *; unfold Rmin in |- *.
  case (Rle_dec x1 (b - a)); intros.
  case (Rle_dec x0 x1); intro.
  apply (cond_pos x0).
  elim H8; intros; assumption.
  case (Rle_dec x0 (b - a)); intro.
  apply (cond_pos x0).
  apply Rlt_Rminus; assumption.
  split with (mkposreal _ H9).
  intros; case (Rcase_abs h0); intro.
  assert (H12 : a + h0 < a).
  pattern a at 2 in |- *; rewrite <- Rplus_0_r; apply Rplus_lt_compat_l;
    assumption.
  unfold primitive in |- *.
  case (Rle_dec a (a + h0)); case (Rle_dec (a + h0) b); case (Rle_dec a a);
  case (Rle_dec a b); intros;
    try (elim n; left; assumption) || (elim n; right; reflexivity).
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ r3 H12)).
  elim n; left; apply Rlt_trans with a; assumption.
  rewrite RiemannInt_P9; replace 0 with (f_a a).
  replace (f a * (a + h0 - a)) with (f_a (a + h0)).
  apply H5; try assumption.
  apply Rlt_le_trans with del;
    [ assumption | unfold del in |- *; apply Rmin_l ].
  unfold f_a in |- *; ring.
  unfold f_a in |- *; ring.
  elim n; left; apply Rlt_trans with a; assumption.
  assert (H12 : a < a + h0).
  pattern a at 1 in |- *; rewrite <- Rplus_0_r; apply Rplus_lt_compat_l.
  assert (H12 := Rge_le _ _ r); elim H12; intro.
  assumption.
  elim H10; symmetry  in |- *; assumption.
  assert (H13 : Riemann_integrable f a (a + h0)).
  apply continuity_implies_RiemannInt.
  left; assumption.
  intros; apply C0; elim H13; intros; split; try assumption.
  apply Rle_trans with (a + h0); try assumption.
  apply Rplus_le_reg_l with (- b - h0).
  replace (- b - h0 + b) with (- h0); [ idtac | ring ].
  replace (- b - h0 + (a + h0)) with (a - b); [ idtac | ring ].
  apply Ropp_le_cancel; rewrite Ropp_involutive; rewrite Ropp_minus_distr;
    apply Rle_trans with del.
  apply Rle_trans with (Rabs h0); [ apply RRle_abs | left; assumption ].
  unfold del in |- *; apply Rle_trans with (Rmin x1 (b - a)); apply Rmin_r.
  replace (primitive h (FTC_P1 h C0) (a + h0) - primitive h (FTC_P1 h C0) a)
    with (RiemannInt H13).
  replace (f a) with (RiemannInt (RiemannInt_P14 a (a + h0) (f a)) / h0).
  replace
  (RiemannInt H13 / h0 - RiemannInt (RiemannInt_P14 a (a + h0) (f a)) / h0)
    with ((RiemannInt H13 - RiemannInt (RiemannInt_P14 a (a + h0) (f a))) / h0).
  replace (RiemannInt H13 - RiemannInt (RiemannInt_P14 a (a + h0) (f a))) with
  (RiemannInt (RiemannInt_P10 (-1) H13 (RiemannInt_P14 a (a + h0) (f a)))).
  unfold Rdiv in |- *; rewrite Rabs_mult;
    apply Rle_lt_trans with
      (RiemannInt
        (RiemannInt_P16
          (RiemannInt_P10 (-1) H13 (RiemannInt_P14 a (a + h0) (f a)))) *
        Rabs (/ h0)).
  do 2 rewrite <- (Rmult_comm (Rabs (/ h0))); apply Rmult_le_compat_l.
  apply Rabs_pos.
  apply
    (RiemannInt_P17 (RiemannInt_P10 (-1) H13 (RiemannInt_P14 a (a + h0) (f a)))
      (RiemannInt_P16
        (RiemannInt_P10 (-1) H13 (RiemannInt_P14 a (a + h0) (f a))))); 
    left; assumption.
  apply Rle_lt_trans with
    (RiemannInt (RiemannInt_P14 a (a + h0) (eps / 2)) * Rabs (/ h0)).
  do 2 rewrite <- (Rmult_comm (Rabs (/ h0))); apply Rmult_le_compat_l.
  apply Rabs_pos.
  apply RiemannInt_P19.
  left; assumption.
  intros; replace (f x2 + -1 * fct_cte (f a) x2) with (f x2 - f a).
  unfold fct_cte in |- *; case (Req_dec a x2); intro.
  rewrite H15; unfold Rminus in |- *; rewrite Rplus_opp_r; rewrite Rabs_R0;
    left; assumption.
  elim H8; intros; left; apply H17; repeat split.
  assumption.
  rewrite Rabs_right.
  apply Rplus_lt_reg_r with a; replace (a + (x2 - a)) with x2; [ idtac | ring ].
  apply Rlt_le_trans with (a + h0).
  elim H14; intros; assumption.
  apply Rplus_le_compat_l; left; apply Rle_lt_trans with (Rabs h0).
  apply RRle_abs.
  apply Rlt_le_trans with del;
    [ assumption
      | unfold del in |- *; apply Rle_trans with (Rmin x1 (b - a));
        [ apply Rmin_r | apply Rmin_l ] ].
  apply Rle_ge; left; apply Rlt_Rminus; elim H14; intros; assumption.
  unfold fct_cte in |- *; ring.
  rewrite RiemannInt_P15.
  rewrite Rmult_assoc; replace ((a + h0 - a) * Rabs (/ h0)) with 1.
  rewrite Rmult_1_r; unfold Rdiv in |- *; apply Rmult_lt_reg_l with 2;
    [ prove_sup0
      | rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
        rewrite <- Rinv_r_sym;
          [ rewrite Rmult_1_l; pattern eps at 1 in |- *; rewrite <- Rplus_0_r;
            rewrite double; apply Rplus_lt_compat_l; assumption
            | discrR ] ].
  rewrite Rabs_right.
  rewrite Rplus_comm; unfold Rminus in |- *; rewrite Rplus_assoc;
    rewrite Rplus_opp_r; rewrite Rplus_0_r; rewrite <- Rinv_r_sym;
      [ reflexivity | assumption ].
  apply Rle_ge; left; apply Rinv_0_lt_compat; assert (H14 := Rge_le _ _ r);
    elim H14; intro.
  assumption.
  elim H10; symmetry  in |- *; assumption.
  rewrite
    (RiemannInt_P13 H13 (RiemannInt_P14 a (a + h0) (f a))
      (RiemannInt_P10 (-1) H13 (RiemannInt_P14 a (a + h0) (f a))))
    ; ring.
  unfold Rdiv, Rminus in |- *; rewrite Rmult_plus_distr_r; ring.
  rewrite RiemannInt_P15.
  rewrite Rplus_comm; unfold Rminus in |- *; rewrite Rplus_assoc;
    rewrite Rplus_opp_r; rewrite Rplus_0_r; unfold Rdiv in |- *;
      rewrite Rmult_assoc; rewrite <- Rinv_r_sym; [ ring | assumption ].
  cut (a <= a + h0).
  cut (a + h0 <= b).
  intros; unfold primitive in |- *; case (Rle_dec a (a + h0));
    case (Rle_dec (a + h0) b); case (Rle_dec a a); case (Rle_dec a b); 
    intros; try (elim n; right; reflexivity) || (elim n; left; assumption).
  rewrite RiemannInt_P9; unfold Rminus in |- *; rewrite Ropp_0;
    rewrite Rplus_0_r; apply RiemannInt_P5.
  elim n; assumption.
  elim n; assumption.
  2: left; assumption.
  apply Rplus_le_reg_l with (- a); replace (- a + (a + h0)) with h0;
    [ idtac | ring ].
  rewrite Rplus_comm; apply Rle_trans with del;
    [ apply Rle_trans with (Rabs h0); [ apply RRle_abs | left; assumption ]
      | unfold del in |- *; apply Rle_trans with (Rmin x1 (b - a)); apply Rmin_r ].
(*****)
  assert (H1 : x = a).
  rewrite <- H0 in H; elim H; intros; apply Rle_antisym; assumption.
  set (f_a := fun x:R => f a * (x - a)).
  assert (H2 : derivable_pt_lim f_a a (f a)).
  unfold f_a in |- *;
    change (derivable_pt_lim (fct_cte (f a) * (id - fct_cte a)%F) a (f a))
      in |- *; pattern (f a) at 2 in |- *;
        replace (f a) with (0 * (id - fct_cte a)%F a + fct_cte (f a) a * 1).
  apply derivable_pt_lim_mult.
  apply derivable_pt_lim_const.
  replace 1 with (1 - 0); [ idtac | ring ].
  apply derivable_pt_lim_minus.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
  unfold fct_cte in |- *; ring.
  set
    (f_b := fun x:R => f b * (x - b) + RiemannInt (FTC_P1 h C0 h (Rle_refl b))).
  assert (H3 : derivable_pt_lim f_b b (f b)).
  unfold f_b in |- *; pattern (f b) at 2 in |- *; replace (f b) with (f b + 0).
  change
    (derivable_pt_lim
      ((fct_cte (f b) * (id - fct_cte b))%F +
        fct_cte (RiemannInt (FTC_P1 h C0 h (Rle_refl b)))) b (
          f b + 0)) in |- *. 
  apply derivable_pt_lim_plus.
  pattern (f b) at 2 in |- *;
    replace (f b) with (0 * (id - fct_cte b)%F b + fct_cte (f b) b * 1).
  apply derivable_pt_lim_mult.
  apply derivable_pt_lim_const.
  replace 1 with (1 - 0); [ idtac | ring ].
  apply derivable_pt_lim_minus.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
  unfold fct_cte in |- *; ring.
  apply derivable_pt_lim_const.
  ring.
  unfold derivable_pt_lim in |- *; intros; elim (H2 _ H4); intros;
    elim (H3 _ H4); intros; set (del := Rmin x0 x1).
  assert (H7 : 0 < del).
  unfold del in |- *; unfold Rmin in |- *; case (Rle_dec x0 x1); intro.
  apply (cond_pos x0).
  apply (cond_pos x1).
  split with (mkposreal _ H7); intros; case (Rcase_abs h0); intro.
  assert (H10 : a + h0 < a).
  pattern a at 2 in |- *; rewrite <- Rplus_0_r; apply Rplus_lt_compat_l;
    assumption.
  rewrite H1; unfold primitive in |- *; case (Rle_dec a (a + h0));
    case (Rle_dec (a + h0) b); case (Rle_dec a a); case (Rle_dec a b); 
    intros; try (elim n; right; assumption || reflexivity).
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ r3 H10)).
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ r2 H10)).
  rewrite RiemannInt_P9; replace 0 with (f_a a).
  replace (f a * (a + h0 - a)) with (f_a (a + h0)).
  apply H5; try assumption.
  apply Rlt_le_trans with del; try assumption.
  unfold del in |- *; apply Rmin_l.
  unfold f_a in |- *; ring.
  unfold f_a in |- *; ring.
  elim n; rewrite <- H0; left; assumption.
  assert (H10 : a < a + h0).
  pattern a at 1 in |- *; rewrite <- Rplus_0_r; apply Rplus_lt_compat_l.
  assert (H10 := Rge_le _ _ r); elim H10; intro.
  assumption.
  elim H8; symmetry  in |- *; assumption.
  rewrite H0 in H1; rewrite H1; unfold primitive in |- *;
    case (Rle_dec a (b + h0)); case (Rle_dec (b + h0) b); 
    case (Rle_dec a b); case (Rle_dec b b); intros;
      try (elim n; right; assumption || reflexivity).
  rewrite H0 in H10; elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ r2 H10)).
  repeat rewrite RiemannInt_P9.
  replace (RiemannInt (FTC_P1 h C0 r1 r0)) with (f_b b).
  fold (f_b (b + h0)) in |- *.
  apply H6; try assumption.
  apply Rlt_le_trans with del; try assumption.
  unfold del in |- *; apply Rmin_r.
  unfold f_b in |- *; unfold Rminus in |- *; rewrite Rplus_opp_r;
    rewrite Rmult_0_r; rewrite Rplus_0_l; apply RiemannInt_P5.
  elim n; rewrite <- H0; left; assumption.
  elim n0; rewrite <- H0; left; assumption.
Qed.

Lemma RiemannInt_P29 :
  forall (f:R -> R) a b (h:a <= b)
    (C0:forall x:R, a <= x <= b -> continuity_pt f x),
    antiderivative f (primitive h (FTC_P1 h C0)) a b.
Proof.
  intro f; intros; unfold antiderivative in |- *; split; try assumption; intros;
    assert (H0 := RiemannInt_P28 h C0 H);
      assert (H1 : derivable_pt (primitive h (FTC_P1 h C0)) x);
        [ unfold derivable_pt in |- *; split with (f x); apply H0
          | split with H1; symmetry  in |- *; apply derive_pt_eq_0; apply H0 ].
Qed.

Lemma RiemannInt_P30 :
  forall (f:R -> R) (a b:R),
    a <= b ->
    (forall x:R, a <= x <= b -> continuity_pt f x) ->
    sigT (fun g:R -> R => antiderivative f g a b).
Proof.
  intros; split with (primitive H (FTC_P1 H H0)); apply RiemannInt_P29.
Qed.

Record C1_fun : Type := mkC1
  {c1 :> R -> R; diff0 : derivable c1; cont1 : continuity (derive c1 diff0)}.

Lemma RiemannInt_P31 :
  forall (f:C1_fun) (a b:R),
    a <= b -> antiderivative (derive f (diff0 f)) f a b.
Proof.
  intro f; intros; unfold antiderivative in |- *; split; try assumption; intros;
    split with (diff0 f x); reflexivity.
Qed.

Lemma RiemannInt_P32 :
  forall (f:C1_fun) (a b:R), Riemann_integrable (derive f (diff0 f)) a b.
Proof.
  intro f; intros; case (Rle_dec a b); intro;
    [ apply continuity_implies_RiemannInt; try assumption; intros;
      apply (cont1 f)
      | assert (H : b <= a);
        [ auto with real
          | apply RiemannInt_P1; apply continuity_implies_RiemannInt;
            try assumption; intros; apply (cont1 f) ] ].
Qed.

Lemma RiemannInt_P33 :
  forall (f:C1_fun) (a b:R) (pr:Riemann_integrable (derive f (diff0 f)) a b),
    a <= b -> RiemannInt pr = f b - f a.
Proof.
  intro f; intros;
    assert
      (H0 : forall x:R, a <= x <= b -> continuity_pt (derive f (diff0 f)) x).
  intros; apply (cont1 f).
  rewrite (RiemannInt_P20 H (FTC_P1 H H0) pr);
    assert (H1 := RiemannInt_P29 H H0); assert (H2 := RiemannInt_P31 f H);
      elim (antiderivative_Ucte (derive f (diff0 f)) _ _ _ _ H1 H2); 
        intros C H3; repeat rewrite H3;
          [ ring
            | split; [ right; reflexivity | assumption ]
            | split; [ assumption | right; reflexivity ] ].
Qed.

Lemma FTC_Riemann :
  forall (f:C1_fun) (a b:R) (pr:Riemann_integrable (derive f (diff0 f)) a b),
    RiemannInt pr = f b - f a.
Proof.
  intro f; intros; case (Rle_dec a b); intro;
    [ apply RiemannInt_P33; assumption
      | assert (H : b <= a);
        [ auto with real
          | assert (H0 := RiemannInt_P1 pr); rewrite (RiemannInt_P8 pr H0);
            rewrite (RiemannInt_P33 _ H0 H); ring ] ].
Qed.

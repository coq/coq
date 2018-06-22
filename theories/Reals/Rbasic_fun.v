(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*********************************************************)
(**          Complements for the real numbers            *)
(*                                                       *)
(*********************************************************)

Require Import Rbase.
Require Import R_Ifp.
Require Import Lra.
Local Open Scope R_scope.

Implicit Type r : R.

(*******************************)
(** *        Rmin              *)
(*******************************)

(*********)
Definition Rmin (x y:R) : R :=
  match Rle_dec x y with
    | left _ => x
    | right _ => y
  end.

(*********)
Lemma Rmin_case : forall r1 r2 (P:R -> Type), P r1 -> P r2 -> P (Rmin r1 r2).
Proof.
  intros r1 r2 P H1 H2; unfold Rmin; case (Rle_dec r1 r2); auto.
Qed.

(*********)
Lemma Rmin_case_strong : forall r1 r2 (P:R -> Type), 
  (r1 <= r2 -> P r1) -> (r2 <= r1 -> P r2) -> P (Rmin r1 r2).
Proof.
  intros r1 r2 P H1 H2; unfold Rmin; destruct (Rle_dec r1 r2); auto with real.
Qed.

(*********)
Lemma Rmin_Rgt_l : forall r1 r2 r, Rmin r1 r2 > r -> r1 > r /\ r2 > r.
Proof.
  intros r1 r2 r; unfold Rmin; case (Rle_dec r1 r2) as [Hle|Hnle]; intros.
  split.
  assumption.
  unfold Rgt; exact (Rlt_le_trans r r1 r2 H Hle).
  split.
  generalize (Rnot_le_lt r1 r2 Hnle); intro; exact (Rgt_trans r1 r2 r H0 H).
  assumption.
Qed.

(*********)
Lemma Rmin_Rgt_r : forall r1 r2 r, r1 > r /\ r2 > r -> Rmin r1 r2 > r.
Proof.
  intros; unfold Rmin; case (Rle_dec r1 r2); elim H; clear H; intros;
    assumption.
Qed.

(*********)
Lemma Rmin_Rgt : forall r1 r2 r, Rmin r1 r2 > r <-> r1 > r /\ r2 > r.
Proof.
  intros; split.
  exact (Rmin_Rgt_l r1 r2 r).
  exact (Rmin_Rgt_r r1 r2 r).
Qed.

(*********)
Lemma Rmin_l : forall x y:R, Rmin x y <= x.
Proof.
  intros; unfold Rmin; case (Rle_dec x y); intro H1;
    [ right; reflexivity | auto with real ].
Qed.

(*********)
Lemma Rmin_r : forall x y:R, Rmin x y <= y.
Proof.
  intros; unfold Rmin; case (Rle_dec x y); intro H1;
    [ assumption | auto with real ].
Qed.

(*********)
Lemma Rmin_left : forall x y, x <= y -> Rmin x y = x.
Proof.
  intros; apply Rmin_case_strong; auto using Rle_antisym.
Qed.

(*********)
Lemma Rmin_right : forall x y, y <= x -> Rmin x y = y.
Proof.
  intros; apply Rmin_case_strong; auto using Rle_antisym.
Qed.

(*********)
Lemma Rle_min_compat_r : forall x y z, x <= y -> Rmin x z <= Rmin y z.
Proof.
  intros; do 2 (apply Rmin_case_strong; intro); eauto using Rle_trans, Rle_refl.
Qed.

(*********)
Lemma Rle_min_compat_l : forall x y z, x <= y -> Rmin z x <= Rmin z y.
Proof.
  intros; do 2 (apply Rmin_case_strong; intro); eauto using Rle_trans, Rle_refl.
Qed.

(*********)
Lemma Rmin_comm : forall x y:R, Rmin x y = Rmin y x.
Proof.
  intros; unfold Rmin; case (Rle_dec x y); case (Rle_dec y x); intros;
    try reflexivity || (apply Rle_antisym; assumption || auto with real).
Qed.

(*********)
Lemma Rmin_stable_in_posreal : forall x y:posreal, 0 < Rmin x y.
Proof.
  intros; apply Rmin_Rgt_r; split; [ apply (cond_pos x) | apply (cond_pos y) ].
Qed.

(*********)
Lemma Rmin_pos : forall x y:R, 0 < x -> 0 < y -> 0 < Rmin x y.
Proof.
  intros; unfold Rmin.
  case (Rle_dec x y); intro; assumption.
Qed.

(*********)
Lemma Rmin_glb : forall x y z:R, z <= x -> z <= y -> z <= Rmin x y.
Proof.
  intros; unfold Rmin; case (Rle_dec x y); intro; assumption.
Qed.

(*********)
Lemma Rmin_glb_lt : forall x y z:R, z < x -> z < y -> z < Rmin x y.
Proof.
  intros; unfold Rmin; case (Rle_dec x y); intro; assumption.
Qed.

(*******************************)
(** *        Rmax              *)
(*******************************)

(*********)
Definition Rmax (x y:R) : R :=
  match Rle_dec x y with
    | left _ => y
    | right _ => x
  end.

(*********)
Lemma Rmax_case : forall r1 r2 (P:R -> Type), P r1 -> P r2 -> P (Rmax r1 r2).
Proof.
  intros r1 r2 P H1 H2; unfold Rmax; case (Rle_dec r1 r2); auto.
Qed.

(*********)
Lemma Rmax_case_strong : forall r1 r2 (P:R -> Type),
  (r2 <= r1 -> P r1) -> (r1 <= r2 -> P r2) -> P (Rmax r1 r2).
Proof.
  intros r1 r2 P H1 H2; unfold Rmax; case (Rle_dec r1 r2); auto with real.
Qed.

(*********)
Lemma Rmax_Rle : forall r1 r2 r, r <= Rmax r1 r2 <-> r <= r1 \/ r <= r2.
Proof.
  intros; split.
  unfold Rmax; case (Rle_dec r1 r2); intros; auto.
  intro; unfold Rmax; case (Rle_dec r1 r2) as [|Hnle]; elim H; clear H; intros;
    auto.
  apply (Rle_trans r r1 r2); auto.
  generalize (Rnot_le_lt r1 r2 Hnle); clear Hnle; intro; unfold Rgt in H0;
    apply (Rlt_le r r1 (Rle_lt_trans r r2 r1 H H0)).
Qed.

Lemma Rmax_comm : forall x y:R, Rmax x y = Rmax y x.
Proof.
  intros p q; unfold Rmax; case (Rle_dec p q); case (Rle_dec q p); auto;
    intros H1 H2; apply Rle_antisym; auto with real.
Qed.

(* begin hide *)
Notation RmaxSym := Rmax_comm (only parsing).
(* end hide *)

(*********)
Lemma Rmax_l : forall x y:R, x <= Rmax x y.
Proof.
  intros; unfold Rmax; case (Rle_dec x y); intro H1;
    [ assumption | auto with real ].
Qed.

(*********)
Lemma Rmax_r : forall x y:R, y <= Rmax x y.
Proof.
  intros; unfold Rmax; case (Rle_dec x y); intro H1;
    [ right; reflexivity | auto with real ].
Qed.

(* begin hide *)
Notation RmaxLess1 := Rmax_l (only parsing).
Notation RmaxLess2 := Rmax_r (only parsing).
(* end hide *)

(*********)
Lemma Rmax_left : forall x y, y <= x -> Rmax x y = x.
Proof.
  intros; apply Rmax_case_strong; auto using Rle_antisym.
Qed.

(*********)
Lemma Rmax_right : forall x y, x <= y -> Rmax x y = y.
Proof.
  intros; apply Rmax_case_strong; auto using Rle_antisym.
Qed.

(*********)
Lemma Rle_max_compat_r : forall x y z, x <= y -> Rmax x z <= Rmax y z.
Proof.
  intros; do 2 (apply Rmax_case_strong; intro); eauto using Rle_trans, Rle_refl.
Qed.

(*********)
Lemma Rle_max_compat_l : forall x y z, x <= y -> Rmax z x <= Rmax z y.
Proof.
  intros; do 2 (apply Rmax_case_strong; intro); eauto using Rle_trans, Rle_refl.
Qed.

(*********)
Lemma RmaxRmult :
  forall (p q:R) r, 0 <= r -> Rmax (r * p) (r * q) = r * Rmax p q.
Proof.
  intros p q r H; unfold Rmax.
  case (Rle_dec p q); case (Rle_dec (r * p) (r * q)); auto; intros H1 H2; auto.
  case H; intros E1.
  case H1; auto with real.
  rewrite <- E1; repeat rewrite Rmult_0_l; auto.
  case H; intros E1.
  case H2; auto with real.
  apply Rmult_le_reg_l with (r := r); auto.
  rewrite <- E1; repeat rewrite Rmult_0_l; auto.
Qed.

(*********)
Lemma Rmax_stable_in_negreal : forall x y:negreal, Rmax x y < 0.
Proof.
  intros; unfold Rmax; case (Rle_dec x y); intro;
    [ apply (cond_neg y) | apply (cond_neg x) ].
Qed.

(*********)
Lemma Rmax_lub : forall x y z:R, x <= z -> y <= z -> Rmax x y <= z.
Proof.
  intros; unfold Rmax; case (Rle_dec x y); intro; assumption.
Qed.

(*********)
Lemma Rmax_lub_lt : forall x y z:R, x < z -> y < z -> Rmax x y < z.
Proof.
  intros; unfold Rmax; case (Rle_dec x y); intro; assumption.
Qed.

Lemma Rmax_Rlt : forall x y z, 
  Rmax x y < z <-> x < z /\ y < z.
Proof.
intros x y z; split.
 unfold Rmax; case (Rle_dec x y).
  intros xy yz; split;[apply Rle_lt_trans with y|]; assumption.
  intros xz xy; split;[|apply Rlt_trans with x;[apply Rnot_le_gt|]];assumption.
 intros [h h']; apply Rmax_lub_lt; assumption.
Qed.

(*********)
Lemma Rmax_neg : forall x y:R, x < 0 -> y < 0 -> Rmax x y < 0.
Proof.
  intros; unfold Rmax.
  case (Rle_dec x y); intro; assumption.
Qed.

(*******************************)
(** *        Rabsolu           *)
(*******************************)

(*********)
Lemma Rcase_abs : forall r, {r < 0} + {r >= 0}.
Proof.
  intro; generalize (Rle_dec 0 r); intro X; elim X; intro H; clear X.
  right; apply (Rle_ge 0 r H).
  left; fold (0 > r); apply (Rnot_le_lt 0 r H).
Qed.

(*********)
Definition Rabs r : R :=
  match Rcase_abs r with
    | left _ => - r
    | right _ => r
  end.

(*********)
Lemma Rabs_R0 : Rabs 0 = 0.
Proof.
  unfold Rabs; case (Rcase_abs 0); auto; intro.
  generalize (Rlt_irrefl 0); intro; exfalso; auto.
Qed.

Lemma Rabs_R1 : Rabs 1 = 1.
Proof.
unfold Rabs; case (Rcase_abs 1); auto with real.
intros H; absurd (1 < 0); auto with real.
Qed.

(*********)
Lemma Rabs_no_R0 : forall r, r <> 0 -> Rabs r <> 0.
Proof.
  intros; unfold Rabs; case (Rcase_abs r); intro; auto.
  apply Ropp_neq_0_compat; auto.
Qed.

(*********)
Lemma Rabs_left : forall r, r < 0 -> Rabs r = - r.
Proof.
  intros; unfold Rabs; case (Rcase_abs r); trivial; intro;
    absurd (r >= 0).
  exact (Rlt_not_ge r 0 H).
  assumption.
Qed.

(*********)
Lemma Rabs_right : forall r, r >= 0 -> Rabs r = r.
Proof.
  intros; unfold Rabs; case (Rcase_abs r) as [Hlt|Hge].
  absurd (r >= 0).
  exact (Rlt_not_ge r 0 Hlt).
  assumption.
  trivial.
Qed.

Lemma Rabs_left1 : forall a:R, a <= 0 -> Rabs a = - a.
Proof.
  intros a H; case H; intros H1.
  apply Rabs_left; auto.
  rewrite H1; simpl; rewrite Rabs_right; auto with real.
Qed.

(*********)
Lemma Rabs_pos : forall x:R, 0 <= Rabs x.
Proof.
  intros; unfold Rabs; case (Rcase_abs x) as [Hlt|Hge].
  generalize (Ropp_lt_gt_contravar x 0 Hlt); intro; unfold Rgt in H;
    rewrite Ropp_0 in H; left; assumption.
  apply Rge_le; assumption.
Qed.

Lemma Rle_abs : forall x:R, x <= Rabs x.
Proof.
  intro; unfold Rabs; case (Rcase_abs x); intros; lra.
Qed.

Definition RRle_abs := Rle_abs.

Lemma Rabs_le : forall a b, -b <= a <= b -> Rabs a <= b.
Proof.
intros a b; unfold Rabs; case Rcase_abs.
 intros _ [it _]; apply Ropp_le_cancel; rewrite Ropp_involutive; exact it.
intros _ [_ it]; exact it.
Qed.

(*********)
Lemma Rabs_pos_eq : forall x:R, 0 <= x -> Rabs x = x.
Proof.
  intros; unfold Rabs; case (Rcase_abs x) as [Hlt|Hge];
    [ generalize (Rgt_not_le 0 x Hlt); intro; exfalso; auto | trivial ].
Qed.

(*********)
Lemma Rabs_Rabsolu : forall x:R, Rabs (Rabs x) = Rabs x.
Proof.
  intro; apply (Rabs_pos_eq (Rabs x) (Rabs_pos x)).
Qed.

(*********)
Lemma Rabs_pos_lt : forall x:R, x <> 0 -> 0 < Rabs x.
Proof.
  intros; destruct (Rabs_pos x) as [|Heq]; auto.
  apply Rabs_no_R0 in H; symmetry in Heq; contradiction.
Qed.

(*********)
Lemma Rabs_minus_sym : forall x y:R, Rabs (x - y) = Rabs (y - x).
Proof.
  intros; unfold Rabs; case (Rcase_abs (x - y)) as [Hlt|Hge];
    case (Rcase_abs (y - x)) as [Hlt'|Hge'].
  apply Rminus_lt, Rlt_asym in Hlt; apply Rminus_lt in Hlt'; contradiction.
  rewrite (Ropp_minus_distr x y); trivial.
  rewrite (Ropp_minus_distr y x); trivial.
  destruct Hge; destruct Hge'.
  apply Ropp_lt_gt_0_contravar in H; rewrite (Ropp_minus_distr x y) in H;
    apply Rlt_asym in H0; contradiction.
  apply Rminus_diag_uniq in H0 as ->; trivial.
  apply Rminus_diag_uniq in H as ->; trivial.
  apply Rminus_diag_uniq in H0 as ->; trivial.
Qed.

(*********)
Lemma Rabs_mult : forall x y:R, Rabs (x * y) = Rabs x * Rabs y.
Proof.
  intros; unfold Rabs; case (Rcase_abs (x * y)) as [Hlt|Hge];
    case (Rcase_abs x) as [Hltx|Hgex];
    case (Rcase_abs y) as [Hlty|Hgey]; auto.
  apply Rmult_lt_gt_compat_neg_l with (r:=x), Rlt_asym in Hlty; trivial.
    rewrite Rmult_0_r in Hlty; contradiction.
  rewrite (Ropp_mult_distr_l_reverse x y); trivial.
  rewrite (Rmult_comm x (- y)); rewrite (Ropp_mult_distr_l_reverse y x);
    rewrite (Rmult_comm x y); trivial.
  destruct Hgex as [| ->], Hgey as [| ->].
  apply Rmult_lt_compat_l with (r:=x), Rlt_asym in H0; trivial.
    rewrite Rmult_0_r in H0; contradiction.
  rewrite Rmult_0_r in Hlt; contradiction (Rlt_irrefl 0).
  rewrite Rmult_0_l in Hlt; contradiction (Rlt_irrefl 0).
  rewrite Rmult_0_l in Hlt; contradiction (Rlt_irrefl 0).
  rewrite (Rmult_opp_opp x y); trivial.
  destruct Hge. destruct Hgey.
  apply Rmult_lt_compat_r with (r:=y), Rlt_asym in Hltx; trivial.
    rewrite Rmult_0_l in Hltx; contradiction.
  rewrite H0, Rmult_0_r in H; contradiction (Rlt_irrefl 0).
  rewrite <- Ropp_mult_distr_l, H, Ropp_0; trivial.
  destruct Hge. destruct Hgex.
  apply Rmult_lt_compat_l with (r:=x), Rlt_asym in Hlty; trivial.
    rewrite Rmult_0_r in Hlty; contradiction.
  rewrite H0, 2!Rmult_0_l; trivial.
  rewrite <- Ropp_mult_distr_r, H, Ropp_0; trivial.
Qed.

(*********)
Lemma Rabs_Rinv : forall r, r <> 0 -> Rabs (/ r) = / Rabs r.
Proof.
  intro; unfold Rabs; case (Rcase_abs r) as [Hlt|Hge];
    case (Rcase_abs (/ r)) as [Hlt'|Hge']; auto;
    intros.
  apply Ropp_inv_permute; auto.
  rewrite <- Ropp_inv_permute; trivial.
  destruct Hge' as [| ->].
  apply Rinv_lt_0_compat, Rlt_asym in Hlt; contradiction.
  rewrite Ropp_0; trivial.
  destruct Hge as [| ->].
  apply Rinv_0_lt_compat, Rlt_asym in H0; contradiction.
  contradiction (refl_equal 0).
Qed.

Lemma Rabs_Ropp : forall x:R, Rabs (- x) = Rabs x.
Proof.
  intro; replace (-x) with (-1 * x) by ring.
  rewrite Rabs_mult.
  replace (Rabs (-1)) with 1.
  apply Rmult_1_l.
  unfold Rabs; case (Rcase_abs (-1)).
  intro; ring.
  rewrite <- Ropp_0.
  intro H0; apply Ropp_ge_cancel in H0.
  elim (Rge_not_lt _ _ H0).
  apply Rlt_0_1.
Qed.

(*********)
Lemma Rabs_triang : forall a b:R, Rabs (a + b) <= Rabs a + Rabs b.
Proof.
  intros a b; unfold Rabs; case (Rcase_abs (a + b)) as [Hlt|Hge];
    case (Rcase_abs a) as [Hlta|Hgea];
    case (Rcase_abs b) as [Hltb|Hgeb].
  apply (Req_le (- (a + b)) (- a + - b)); rewrite (Ropp_plus_distr a b);
    reflexivity.
(**)
  rewrite (Ropp_plus_distr a b); apply (Rplus_le_compat_l (- a) (- b) b);
    unfold Rle; elim Hgeb; intro.
  left; unfold Rgt in H; generalize (Rplus_lt_compat_l (- b) 0 b H); intro;
    elim (Rplus_ne (- b)); intros v w; rewrite v in H0;
      clear v w; rewrite (Rplus_opp_l b) in H0; apply (Rlt_trans (- b) 0 b H0 H).
  right; rewrite H; apply Ropp_0.
(**)
  rewrite (Ropp_plus_distr a b); rewrite (Rplus_comm (- a) (- b));
    rewrite (Rplus_comm a (- b)); apply (Rplus_le_compat_l (- b) (- a) a);
      unfold Rle; elim Hgea; intro.
  left; unfold Rgt in H; generalize (Rplus_lt_compat_l (- a) 0 a H); intro;
    elim (Rplus_ne (- a)); intros v w; rewrite v in H0;
      clear v w; rewrite (Rplus_opp_l a) in H0; apply (Rlt_trans (- a) 0 a H0 H).
  right; rewrite H; apply Ropp_0.
(**)
  exfalso; generalize (Rplus_ge_compat_l a b 0 Hgeb); intro;
    elim (Rplus_ne a); intros v w; rewrite v in H; clear v w;
      generalize (Rge_trans (a + b) a 0 H Hgea); intro; clear H;
        unfold Rge in H0; elim H0; intro; clear H0.
  unfold Rgt in H; generalize (Rlt_asym (a + b) 0 Hlt); intro; auto.
  absurd (a + b = 0); auto.
  apply (Rlt_dichotomy_converse (a + b) 0); left; assumption.
(**)
  exfalso; generalize (Rplus_lt_compat_l a b 0 Hltb); intro;
    elim (Rplus_ne a); intros v w; rewrite v in H; clear v w;
      generalize (Rlt_trans (a + b) a 0 H Hlta); intro; clear H;
        destruct Hge.
  unfold Rgt in H; generalize (Rlt_trans (a + b) 0 (a + b) H0 H); intro;
    apply (Rlt_irrefl (a + b)); assumption.
  rewrite H in H0; apply (Rlt_irrefl 0); assumption.
(**)
  rewrite (Rplus_comm a b); rewrite (Rplus_comm (- a) b);
    apply (Rplus_le_compat_l b a (- a)); apply (Rminus_le a (- a));
      unfold Rminus; rewrite (Ropp_involutive a);
        generalize (Rplus_lt_compat_l a a 0 Hlta); clear Hge Hgeb;
          intro; elim (Rplus_ne a); intros v w; rewrite v in H;
            clear v w; generalize (Rlt_trans (a + a) a 0 H Hlta);
              intro; apply (Rlt_le (a + a) 0 H0).
(**)
  apply (Rplus_le_compat_l a b (- b)); apply (Rminus_le b (- b));
    unfold Rminus; rewrite (Ropp_involutive b);
      generalize (Rplus_lt_compat_l b b 0 Hltb); clear Hge Hgea;
        intro; elim (Rplus_ne b); intros v w; rewrite v in H;
          clear v w; generalize (Rlt_trans (b + b) b 0 H Hltb);
            intro; apply (Rlt_le (b + b) 0 H0).
(**)
  unfold Rle; right; reflexivity.
Qed.

(*********)
Lemma Rabs_triang_inv : forall a b:R, Rabs a - Rabs b <= Rabs (a - b).
Proof.
  intros; apply (Rplus_le_reg_l (Rabs b) (Rabs a - Rabs b) (Rabs (a - b)));
    unfold Rminus; rewrite <- (Rplus_assoc (Rabs b) (Rabs a) (- Rabs b));
      rewrite (Rplus_comm (Rabs b) (Rabs a));
        rewrite (Rplus_assoc (Rabs a) (Rabs b) (- Rabs b));
          rewrite (Rplus_opp_r (Rabs b)); rewrite (proj1 (Rplus_ne (Rabs a)));
            replace (Rabs a) with (Rabs (a + 0)).
  rewrite <- (Rplus_opp_r b); rewrite <- (Rplus_assoc a b (- b));
    rewrite (Rplus_comm a b); rewrite (Rplus_assoc b a (- b)).
  exact (Rabs_triang b (a + - b)).
  rewrite (proj1 (Rplus_ne a)); trivial.
Qed.

(* ||a|-|b||<=|a-b| *)
Lemma Rabs_triang_inv2 : forall a b:R, Rabs (Rabs a - Rabs b) <= Rabs (a - b).
Proof.
  cut
    (forall a b:R, Rabs b <= Rabs a -> Rabs (Rabs a - Rabs b) <= Rabs (a - b)).
  intros; destruct (Rtotal_order (Rabs a) (Rabs b)) as [Hlt| [Heq| Hgt]].
  rewrite <- (Rabs_Ropp (Rabs a - Rabs b)); rewrite <- (Rabs_Ropp (a - b));
    do 2 rewrite Ropp_minus_distr.
  apply H; left; assumption.
  rewrite Heq; unfold Rminus; rewrite Rplus_opp_r; rewrite Rabs_R0;
    apply Rabs_pos.
  apply H; left; assumption.
  intros; replace (Rabs (Rabs a - Rabs b)) with (Rabs a - Rabs b).
  apply Rabs_triang_inv.
  rewrite (Rabs_right (Rabs a - Rabs b));
    [ reflexivity
      | apply Rle_ge; apply Rplus_le_reg_l with (Rabs b); rewrite Rplus_0_r;
        replace (Rabs b + (Rabs a - Rabs b)) with (Rabs a);
        [ assumption | ring ] ].
Qed.

(*********)
Lemma Rabs_def1 : forall x a:R, x < a -> - a < x -> Rabs x < a.
Proof.
  unfold Rabs; intros; case (Rcase_abs x); intro.
  generalize (Ropp_lt_gt_contravar (- a) x H0); unfold Rgt;
    rewrite Ropp_involutive; intro; assumption.
  assumption.
Qed.

(*********)
Lemma Rabs_def2 : forall x a:R, Rabs x < a -> x < a /\ - a < x.
Proof.
  unfold Rabs; intro x; case (Rcase_abs x) as [Hlt|Hge]; intros.
  generalize (Ropp_gt_lt_0_contravar x Hlt); unfold Rgt; intro;
    generalize (Rlt_trans 0 (- x) a H0 H); intro; split.
  apply (Rlt_trans x 0 a Hlt H1).
  generalize (Ropp_lt_gt_contravar (- x) a H); rewrite (Ropp_involutive x);
    unfold Rgt; trivial.
  fold (a > x) in H; generalize (Rgt_ge_trans a x 0 H Hge); intro;
    generalize (Ropp_lt_gt_0_contravar a H0); intro; fold (0 > - a);
      generalize (Rge_gt_trans x 0 (- a) Hge H1); unfold Rgt;
        intro; split; assumption.
Qed.

Lemma RmaxAbs :
  forall (p q:R) r, p <= q -> q <= r -> Rabs q <= Rmax (Rabs p) (Rabs r).
Proof.
  intros p q r H' H'0; case (Rle_or_lt 0 p); intros H'1.
  repeat rewrite Rabs_right; auto with real.
  apply Rle_trans with r; auto with real.
  apply RmaxLess2; auto.
  apply Rge_trans with p; auto with real; apply Rge_trans with q;
    auto with real.
  apply Rge_trans with p; auto with real.
  rewrite (Rabs_left p); auto.
  case (Rle_or_lt 0 q); intros H'2.
  repeat rewrite Rabs_right; auto with real.
  apply Rle_trans with r; auto.
  apply RmaxLess2; auto.
  apply Rge_trans with q; auto with real.
  rewrite (Rabs_left q); auto.
  case (Rle_or_lt 0 r); intros H'3.
  repeat rewrite Rabs_right; auto with real.
  apply Rle_trans with (- p); auto with real.
  apply RmaxLess1; auto.
  rewrite (Rabs_left r); auto.
  apply Rle_trans with (- p); auto with real.
  apply RmaxLess1; auto.
Qed.

Lemma Rabs_Zabs : forall z:Z, Rabs (IZR z) = IZR (Z.abs z).
Proof.
  intros z; case z; unfold Z.abs.
  apply Rabs_R0.
  now intros p0; apply Rabs_pos_eq, (IZR_le 0).
  unfold IZR at 1.
  intros p0; rewrite Rabs_Ropp.
  now apply Rabs_pos_eq, (IZR_le 0).
Qed.

Lemma abs_IZR : forall z, IZR (Z.abs z) = Rabs (IZR z).
Proof.
  intros.
  now rewrite Rabs_Zabs.
Qed.

Lemma Ropp_Rmax : forall x y, - Rmax x y = Rmin (-x) (-y).
intros x y; apply Rmax_case_strong.
 now intros w; rewrite Rmin_left;[ | apply Rge_le, Ropp_le_ge_contravar].
now intros w; rewrite Rmin_right; [ | apply Rge_le, Ropp_le_ge_contravar].
Qed.

Lemma Ropp_Rmin : forall x y, - Rmin x y = Rmax (-x) (-y).
intros x y; apply Rmin_case_strong.
 now intros w; rewrite Rmax_left;[ | apply Rge_le, Ropp_le_ge_contravar].
now intros w; rewrite Rmax_right; [ | apply Rge_le, Ropp_le_ge_contravar].
Qed.

Lemma Rmax_assoc : forall a b c, Rmax a (Rmax b c) = Rmax (Rmax a b) c.
Proof.
intros a b c.
unfold Rmax; destruct (Rle_dec b c); destruct (Rle_dec a b);
  destruct (Rle_dec a c); destruct (Rle_dec b c); auto with real;
  match goal with 
  | id :  ~ ?x <= ?y, id2 : ?x <= ?z |- _ =>
   case id; apply Rle_trans with z; auto with real
  | id : ~ ?x <= ?y, id2 : ~ ?z <= ?x |- _ =>
   case id; apply Rle_trans with z; auto with real
  end.
Qed.

Lemma Rminmax : forall a b, Rmin a b <= Rmax a b.
Proof.
intros a b; destruct (Rle_dec a b).
 rewrite Rmin_left, Rmax_right; assumption.
now rewrite Rmin_right, Rmax_left; assumption ||
  apply Rlt_le, Rnot_le_gt.
Qed.

Lemma Rmin_assoc : forall x y z, Rmin x (Rmin y z) =
  Rmin (Rmin x y) z.
Proof.
intros a b c.
unfold Rmin; destruct (Rle_dec b c); destruct (Rle_dec a b);
  destruct (Rle_dec a c); destruct (Rle_dec b c); auto with real;
  match goal with 
  | id :  ~ ?x <= ?y, id2 : ?x <= ?z |- _ =>
   case id; apply Rle_trans with z; auto with real
  | id : ~ ?x <= ?y, id2 : ~ ?z <= ?x |- _ =>
   case id; apply Rle_trans with z; auto with real
  end.
Qed.


(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*********************************************************)
(**          Complements for the real numbers            *)
(*                                                       *)
(*********************************************************)

Require Import Rbase.
Require Import R_Ifp.
Require Import Fourier.
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
  intros r1 r2 r; unfold Rmin in |- *; case (Rle_dec r1 r2); intros.
  split.
  assumption.
  unfold Rgt in |- *; unfold Rgt in H; exact (Rlt_le_trans r r1 r2 H r0).
  split.
  generalize (Rnot_le_lt r1 r2 n); intro; exact (Rgt_trans r1 r2 r H0 H).
  assumption.
Qed.

(*********)
Lemma Rmin_Rgt_r : forall r1 r2 r, r1 > r /\ r2 > r -> Rmin r1 r2 > r.
Proof.
  intros; unfold Rmin in |- *; case (Rle_dec r1 r2); elim H; clear H; intros;
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
  intros; unfold Rmin in |- *; case (Rle_dec x y); intro H1;
    [ right; reflexivity | auto with real ].
Qed.

(*********)
Lemma Rmin_r : forall x y:R, Rmin x y <= y.
Proof.
  intros; unfold Rmin in |- *; case (Rle_dec x y); intro H1;
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
  intros; unfold Rmin in |- *.
  case (Rle_dec x y); intro; assumption.
Qed.

(*********)
Lemma Rmin_glb : forall x y z:R, z <= x -> z <= y -> z <= Rmin x y.
Proof.
  intros; unfold Rmin in |- *; case (Rle_dec x y); intro; assumption.
Qed.

(*********)
Lemma Rmin_glb_lt : forall x y z:R, z < x -> z < y -> z < Rmin x y.
Proof.
  intros; unfold Rmin in |- *; case (Rle_dec x y); intro; assumption.
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
  unfold Rmax in |- *; case (Rle_dec r1 r2); intros; auto.
  intro; unfold Rmax in |- *; case (Rle_dec r1 r2); elim H; clear H; intros;
    auto.
  apply (Rle_trans r r1 r2); auto.
  generalize (Rnot_le_lt r1 r2 n); clear n; intro; unfold Rgt in H0;
    apply (Rlt_le r r1 (Rle_lt_trans r r2 r1 H H0)).
Qed.

Lemma Rmax_comm : forall x y:R, Rmax x y = Rmax y x.
Proof.
  intros p q; unfold Rmax in |- *; case (Rle_dec p q); case (Rle_dec q p); auto;
    intros H1 H2; apply Rle_antisym; auto with real.
Qed.

(* begin hide *)
Notation RmaxSym := Rmax_comm (only parsing).
(* end hide *)

(*********)
Lemma Rmax_l : forall x y:R, x <= Rmax x y.
Proof.
  intros; unfold Rmax in |- *; case (Rle_dec x y); intro H1;
    [ assumption | auto with real ].
Qed.

(*********)
Lemma Rmax_r : forall x y:R, y <= Rmax x y.
Proof.
  intros; unfold Rmax in |- *; case (Rle_dec x y); intro H1;
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
  intros p q r H; unfold Rmax in |- *.
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
  intros; unfold Rmax in |- *; case (Rle_dec x y); intro;
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

(*********)
Lemma Rmax_neg : forall x y:R, x < 0 -> y < 0 -> Rmax x y < 0.
Proof.
  intros; unfold Rmax in |- *.
  case (Rle_dec x y); intro; assumption.
Qed.

(*******************************)
(** *        Rabsolu           *)
(*******************************)

(*********)
Lemma Rcase_abs : forall r, {r < 0} + {r >= 0}.
Proof.
  intro; generalize (Rle_dec 0 r); intro X; elim X; intro; clear X.
  right; apply (Rle_ge 0 r a).
  left; fold (0 > r) in |- *; apply (Rnot_le_lt 0 r b).
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
  unfold Rabs in |- *; case (Rcase_abs 0); auto; intro.
  generalize (Rlt_irrefl 0); intro; exfalso; auto.
Qed.

Lemma Rabs_R1 : Rabs 1 = 1.
Proof.
unfold Rabs in |- *; case (Rcase_abs 1); auto with real.
intros H; absurd (1 < 0); auto with real.
Qed.

(*********)
Lemma Rabs_no_R0 : forall r, r <> 0 -> Rabs r <> 0.
Proof.
  intros; unfold Rabs in |- *; case (Rcase_abs r); intro; auto.
  apply Ropp_neq_0_compat; auto.
Qed.

(*********)
Lemma Rabs_left : forall r, r < 0 -> Rabs r = - r.
Proof.
  intros; unfold Rabs in |- *; case (Rcase_abs r); trivial; intro;
    absurd (r >= 0).
  exact (Rlt_not_ge r 0 H).
  assumption.
Qed.

(*********)
Lemma Rabs_right : forall r, r >= 0 -> Rabs r = r.
Proof.
  intros; unfold Rabs in |- *; case (Rcase_abs r); intro.
  absurd (r >= 0).
  exact (Rlt_not_ge r 0 r0).
  assumption.
  trivial.
Qed.

Lemma Rabs_left1 : forall a:R, a <= 0 -> Rabs a = - a.
Proof.
  intros a H; case H; intros H1.
  apply Rabs_left; auto.
  rewrite H1; simpl in |- *; rewrite Rabs_right; auto with real.
Qed.

(*********)
Lemma Rabs_pos : forall x:R, 0 <= Rabs x.
Proof.
  intros; unfold Rabs in |- *; case (Rcase_abs x); intro.
  generalize (Ropp_lt_gt_contravar x 0 r); intro; unfold Rgt in H;
    rewrite Ropp_0 in H; unfold Rle in |- *; left; assumption.
  apply Rge_le; assumption.
Qed.

Lemma Rle_abs : forall x:R, x <= Rabs x.
Proof.
  intro; unfold Rabs in |- *; case (Rcase_abs x); intros; fourier.
Qed.

Definition RRle_abs := Rle_abs.

(*********)
Lemma Rabs_pos_eq : forall x:R, 0 <= x -> Rabs x = x.
Proof.
  intros; unfold Rabs in |- *; case (Rcase_abs x); intro;
    [ generalize (Rgt_not_le 0 x r); intro; exfalso; auto | trivial ].
Qed.

(*********)
Lemma Rabs_Rabsolu : forall x:R, Rabs (Rabs x) = Rabs x.
Proof.
  intro; apply (Rabs_pos_eq (Rabs x) (Rabs_pos x)).
Qed.

(*********)
Lemma Rabs_pos_lt : forall x:R, x <> 0 -> 0 < Rabs x.
Proof.
  intros; generalize (Rabs_pos x); intro; unfold Rle in H0; elim H0; intro;
    auto.
  exfalso; clear H0; elim H; clear H; generalize H1; unfold Rabs in |- *;
    case (Rcase_abs x); intros; auto.
  clear r H1; generalize (Rplus_eq_compat_l x 0 (- x) H0);
    rewrite (let (H1, H2) := Rplus_ne x in H1); rewrite (Rplus_opp_r x);
      trivial.
Qed.

(*********)
Lemma Rabs_minus_sym : forall x y:R, Rabs (x - y) = Rabs (y - x).
Proof.
  intros; unfold Rabs in |- *; case (Rcase_abs (x - y));
    case (Rcase_abs (y - x)); intros.
  generalize (Rminus_lt y x r); generalize (Rminus_lt x y r0); intros;
    generalize (Rlt_asym x y H); intro; exfalso;
      auto.
  rewrite (Ropp_minus_distr x y); trivial.
  rewrite (Ropp_minus_distr y x); trivial.
  unfold Rge in r, r0; elim r; elim r0; intros; clear r r0.
  generalize (Ropp_lt_gt_0_contravar (x - y) H); rewrite (Ropp_minus_distr x y);
    intro; unfold Rgt in H0; generalize (Rlt_asym 0 (y - x) H0);
      intro; exfalso; auto.
  rewrite (Rminus_diag_uniq x y H); trivial.
  rewrite (Rminus_diag_uniq y x H0); trivial.
  rewrite (Rminus_diag_uniq y x H0); trivial.
Qed.

(*********)
Lemma Rabs_mult : forall x y:R, Rabs (x * y) = Rabs x * Rabs y.
Proof.
  intros; unfold Rabs in |- *; case (Rcase_abs (x * y)); case (Rcase_abs x);
    case (Rcase_abs y); intros; auto.
  generalize (Rmult_lt_gt_compat_neg_l y x 0 r r0); intro;
    rewrite (Rmult_0_r y) in H; generalize (Rlt_asym (x * y) 0 r1);
      intro; unfold Rgt in H; exfalso; rewrite (Rmult_comm y x) in H;
        auto.
  rewrite (Ropp_mult_distr_l_reverse x y); trivial.
  rewrite (Rmult_comm x (- y)); rewrite (Ropp_mult_distr_l_reverse y x);
    rewrite (Rmult_comm x y); trivial.
  unfold Rge in r, r0; elim r; elim r0; clear r r0; intros; unfold Rgt in H, H0.
  generalize (Rmult_lt_compat_l x 0 y H H0); intro; rewrite (Rmult_0_r x) in H1;
    generalize (Rlt_asym (x * y) 0 r1); intro; exfalso;
      auto.
  rewrite H in r1; rewrite (Rmult_0_l y) in r1; generalize (Rlt_irrefl 0);
    intro; exfalso; auto.
  rewrite H0 in r1; rewrite (Rmult_0_r x) in r1; generalize (Rlt_irrefl 0);
    intro; exfalso; auto.
  rewrite H0 in r1; rewrite (Rmult_0_r x) in r1; generalize (Rlt_irrefl 0);
    intro; exfalso; auto.
  rewrite (Rmult_opp_opp x y); trivial.
  unfold Rge in r, r1; elim r; elim r1; clear r r1; intros; unfold Rgt in H0, H.
  generalize (Rmult_lt_compat_l y x 0 H0 r0); intro;
    rewrite (Rmult_0_r y) in H1; rewrite (Rmult_comm y x) in H1;
      generalize (Rlt_asym (x * y) 0 H1); intro; exfalso;
        auto.
  generalize (Rlt_dichotomy_converse x 0 (or_introl (x > 0) r0));
    generalize (Rlt_dichotomy_converse y 0 (or_intror (y < 0) H0));
      intros; generalize (Rmult_integral x y H); intro;
        elim H3; intro; exfalso; auto.
  rewrite H0 in H; rewrite (Rmult_0_r x) in H; unfold Rgt in H;
    generalize (Rlt_irrefl 0); intro; exfalso;
      auto.
  rewrite H0; rewrite (Rmult_0_r x); rewrite (Rmult_0_r (- x)); trivial.
  unfold Rge in r0, r1; elim r0; elim r1; clear r0 r1; intros;
    unfold Rgt in H0, H.
  generalize (Rmult_lt_compat_l x y 0 H0 r); intro; rewrite (Rmult_0_r x) in H1;
    generalize (Rlt_asym (x * y) 0 H1); intro; exfalso;
      auto.
  generalize (Rlt_dichotomy_converse y 0 (or_introl (y > 0) r));
    generalize (Rlt_dichotomy_converse 0 x (or_introl (0 > x) H0));
      intros; generalize (Rmult_integral x y H); intro;
        elim H3; intro; exfalso; auto.
  rewrite H0 in H; rewrite (Rmult_0_l y) in H; unfold Rgt in H;
    generalize (Rlt_irrefl 0); intro; exfalso;
      auto.
  rewrite H0; rewrite (Rmult_0_l y); rewrite (Rmult_0_l (- y)); trivial.
Qed.

(*********)
Lemma Rabs_Rinv : forall r, r <> 0 -> Rabs (/ r) = / Rabs r.
Proof.
  intro; unfold Rabs in |- *; case (Rcase_abs r); case (Rcase_abs (/ r)); auto;
    intros.
  apply Ropp_inv_permute; auto.
  generalize (Rinv_lt_0_compat r r1); intro; unfold Rge in r0; elim r0; intros.
  unfold Rgt in H1; generalize (Rlt_asym 0 (/ r) H1); intro; exfalso;
    auto.
  generalize (Rlt_dichotomy_converse (/ r) 0 (or_introl (/ r > 0) H0)); intro;
    exfalso; auto.
  unfold Rge in r1; elim r1; clear r1; intro.
  unfold Rgt in H0; generalize (Rlt_asym 0 (/ r) (Rinv_0_lt_compat r H0));
    intro; exfalso; auto.
  exfalso; auto.
Qed.

Lemma Rabs_Ropp : forall x:R, Rabs (- x) = Rabs x.
Proof.
  intro; cut (- x = -1 * x).
  intros; rewrite H.
  rewrite Rabs_mult.
  cut (Rabs (-1) = 1).
  intros; rewrite H0.
  ring.
  unfold Rabs in |- *; case (Rcase_abs (-1)).
  intro; ring.
  intro H0; generalize (Rge_le (-1) 0 H0); intros.
  generalize (Ropp_le_ge_contravar 0 (-1) H1).
  rewrite Ropp_involutive; rewrite Ropp_0.
  intro; generalize (Rgt_not_le 1 0 Rlt_0_1); intro; generalize (Rge_le 0 1 H2);
    intro; exfalso; auto.
  ring.
Qed.

(*********)
Lemma Rabs_triang : forall a b:R, Rabs (a + b) <= Rabs a + Rabs b.
Proof.
  intros a b; unfold Rabs in |- *; case (Rcase_abs (a + b)); case (Rcase_abs a);
    case (Rcase_abs b); intros.
  apply (Req_le (- (a + b)) (- a + - b)); rewrite (Ropp_plus_distr a b);
    reflexivity.
(**)
  rewrite (Ropp_plus_distr a b); apply (Rplus_le_compat_l (- a) (- b) b);
    unfold Rle in |- *; unfold Rge in r; elim r; intro.
  left; unfold Rgt in H; generalize (Rplus_lt_compat_l (- b) 0 b H); intro;
    elim (Rplus_ne (- b)); intros v w; rewrite v in H0;
      clear v w; rewrite (Rplus_opp_l b) in H0; apply (Rlt_trans (- b) 0 b H0 H).
  right; rewrite H; apply Ropp_0.
(**)
  rewrite (Ropp_plus_distr a b); rewrite (Rplus_comm (- a) (- b));
    rewrite (Rplus_comm a (- b)); apply (Rplus_le_compat_l (- b) (- a) a);
      unfold Rle in |- *; unfold Rge in r0; elim r0; intro.
  left; unfold Rgt in H; generalize (Rplus_lt_compat_l (- a) 0 a H); intro;
    elim (Rplus_ne (- a)); intros v w; rewrite v in H0;
      clear v w; rewrite (Rplus_opp_l a) in H0; apply (Rlt_trans (- a) 0 a H0 H).
  right; rewrite H; apply Ropp_0.
(**)
  exfalso; generalize (Rplus_ge_compat_l a b 0 r); intro;
    elim (Rplus_ne a); intros v w; rewrite v in H; clear v w;
      generalize (Rge_trans (a + b) a 0 H r0); intro; clear H;
        unfold Rge in H0; elim H0; intro; clear H0.
  unfold Rgt in H; generalize (Rlt_asym (a + b) 0 r1); intro; auto.
  absurd (a + b = 0); auto.
  apply (Rlt_dichotomy_converse (a + b) 0); left; assumption.
(**)
  exfalso; generalize (Rplus_lt_compat_l a b 0 r); intro;
    elim (Rplus_ne a); intros v w; rewrite v in H; clear v w;
      generalize (Rlt_trans (a + b) a 0 H r0); intro; clear H;
        unfold Rge in r1; elim r1; clear r1; intro.
  unfold Rgt in H; generalize (Rlt_trans (a + b) 0 (a + b) H0 H); intro;
    apply (Rlt_irrefl (a + b)); assumption.
  rewrite H in H0; apply (Rlt_irrefl 0); assumption.
(**)
  rewrite (Rplus_comm a b); rewrite (Rplus_comm (- a) b);
    apply (Rplus_le_compat_l b a (- a)); apply (Rminus_le a (- a));
      unfold Rminus in |- *; rewrite (Ropp_involutive a);
        generalize (Rplus_lt_compat_l a a 0 r0); clear r r1;
          intro; elim (Rplus_ne a); intros v w; rewrite v in H;
            clear v w; generalize (Rlt_trans (a + a) a 0 H r0);
              intro; apply (Rlt_le (a + a) 0 H0).
(**)
  apply (Rplus_le_compat_l a b (- b)); apply (Rminus_le b (- b));
    unfold Rminus in |- *; rewrite (Ropp_involutive b);
      generalize (Rplus_lt_compat_l b b 0 r); clear r0 r1;
        intro; elim (Rplus_ne b); intros v w; rewrite v in H;
          clear v w; generalize (Rlt_trans (b + b) b 0 H r);
            intro; apply (Rlt_le (b + b) 0 H0).
(**)
  unfold Rle in |- *; right; reflexivity.
Qed.

(*********)
Lemma Rabs_triang_inv : forall a b:R, Rabs a - Rabs b <= Rabs (a - b).
Proof.
  intros; apply (Rplus_le_reg_l (Rabs b) (Rabs a - Rabs b) (Rabs (a - b)));
    unfold Rminus in |- *; rewrite <- (Rplus_assoc (Rabs b) (Rabs a) (- Rabs b));
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
  rewrite Heq; unfold Rminus in |- *; rewrite Rplus_opp_r; rewrite Rabs_R0;
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
  unfold Rabs in |- *; intros; case (Rcase_abs x); intro.
  generalize (Ropp_lt_gt_contravar (- a) x H0); unfold Rgt in |- *;
    rewrite Ropp_involutive; intro; assumption.
  assumption.
Qed.

(*********)
Lemma Rabs_def2 : forall x a:R, Rabs x < a -> x < a /\ - a < x.
Proof.
  unfold Rabs in |- *; intro x; case (Rcase_abs x); intros.
  generalize (Ropp_gt_lt_0_contravar x r); unfold Rgt in |- *; intro;
    generalize (Rlt_trans 0 (- x) a H0 H); intro; split.
  apply (Rlt_trans x 0 a r H1).
  generalize (Ropp_lt_gt_contravar (- x) a H); rewrite (Ropp_involutive x);
    unfold Rgt in |- *; trivial.
  fold (a > x) in H; generalize (Rgt_ge_trans a x 0 H r); intro;
    generalize (Ropp_lt_gt_0_contravar a H0); intro; fold (0 > - a) in |- *;
      generalize (Rge_gt_trans x 0 (- a) r H1); unfold Rgt in |- *;
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

Lemma Rabs_Zabs : forall z:Z, Rabs (IZR z) = IZR (Zabs z).
Proof.
  intros z; case z; simpl in |- *; auto with real.
  apply Rabs_right; auto with real.
  intros p0; apply Rabs_right; auto with real zarith.
  intros p0; rewrite Rabs_Ropp.
  apply Rabs_right; auto with real zarith.
Qed.

Lemma abs_IZR : forall z, IZR (Zabs z) = Rabs (IZR z).
Proof.
  intros.
  now rewrite Rabs_Zabs.
Qed.

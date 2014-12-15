
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

Set Implicit Arguments.

Require Import ZArith.
Require Import BigNumPrelude.
Require Import DoubleType.
Require Import DoubleBase.

Local Open Scope Z_scope.

Section DoubleSub.
 Variable w : Type.
 Variable w_0 : w.
 Variable w_Bm1 : w.
 Variable w_WW : w -> w -> zn2z w.
 Variable ww_Bm1 : zn2z w.
 Variable w_opp_c : w -> carry w.
 Variable w_opp_carry : w -> w.
 Variable w_pred_c : w -> carry w.
 Variable w_sub_c : w -> w -> carry w.
 Variable w_sub_carry_c : w -> w -> carry w.
 Variable w_opp : w -> w.
 Variable w_pred : w -> w.
 Variable w_sub : w -> w -> w.
 Variable w_sub_carry : w -> w -> w.

 (* ** Opposites ** *)
 Definition ww_opp_c x :=
  match x with
  | W0 => C0 W0
  | WW xh xl =>
    match w_opp_c xl with
    | C0 _ =>
      match w_opp_c xh with
      | C0 h => C0 W0
      | C1 h => C1 (WW h w_0)
      end
    | C1 l => C1 (WW (w_opp_carry xh) l)
    end
  end.

 Definition ww_opp x :=
  match x with
  | W0 => W0
  | WW xh xl =>
    match w_opp_c xl with
    | C0 _ => WW (w_opp xh) w_0
    | C1 l => WW (w_opp_carry xh) l
    end
  end.

 Definition ww_opp_carry x :=
  match x with
  | W0 => ww_Bm1
  | WW xh xl => w_WW (w_opp_carry xh) (w_opp_carry xl)
  end.

 Definition ww_pred_c x :=
  match x with
  | W0 => C1 ww_Bm1
  | WW xh xl =>
    match w_pred_c xl with
    | C0 l => C0 (w_WW xh l)
    | C1 _ =>
      match w_pred_c xh with
      | C0 h => C0 (WW h w_Bm1)
      | C1 _ => C1 ww_Bm1
      end
    end
  end.

 Definition ww_pred x :=
  match x with
  | W0 => ww_Bm1
  | WW xh xl =>
    match w_pred_c xl with
    | C0 l => w_WW xh l
    | C1 l => WW (w_pred xh) w_Bm1
    end
  end.

 Definition ww_sub_c x y :=
  match y, x with
  | W0, _ => C0 x
  | WW yh yl, W0 => ww_opp_c (WW yh yl)
  | WW yh yl, WW xh xl =>
    match w_sub_c xl yl with
    | C0 l =>
      match w_sub_c xh yh with
      | C0 h => C0 (w_WW h l)
      | C1 h => C1 (WW h l)
      end
    | C1 l =>
      match w_sub_carry_c xh yh with
      | C0 h => C0 (WW h l)
      | C1 h => C1 (WW h l)
      end
    end
  end.

 Definition ww_sub x y :=
  match y, x with
  | W0, _ => x
  | WW yh yl, W0 => ww_opp (WW yh yl)
  | WW yh yl, WW xh xl =>
    match w_sub_c xl yl with
    | C0 l => w_WW (w_sub xh yh) l
    | C1 l => WW (w_sub_carry xh yh) l
    end
  end.

 Definition ww_sub_carry_c x y :=
  match y, x with
  | W0, W0 => C1 ww_Bm1
  | W0, WW xh xl => ww_pred_c (WW xh xl)
  | WW yh yl, W0 => C1 (ww_opp_carry (WW yh yl))
  | WW yh yl, WW xh xl =>
    match w_sub_carry_c xl yl with
    | C0 l =>
      match w_sub_c xh yh with
      | C0 h => C0 (w_WW h l)
      | C1 h => C1 (WW h l)
      end
    | C1 l =>
      match w_sub_carry_c xh yh with
      | C0 h => C0 (w_WW h l)
      | C1 h => C1 (w_WW h l)
      end
    end
  end.

 Definition ww_sub_carry x y :=
  match y, x with
  | W0, W0 => ww_Bm1
  | W0, WW xh xl => ww_pred (WW xh xl)
  | WW yh yl, W0 => ww_opp_carry (WW yh yl)
  | WW yh yl, WW xh xl =>
    match w_sub_carry_c xl yl with
    | C0 l => w_WW (w_sub xh yh) l
    | C1 l => w_WW (w_sub_carry xh yh) l
    end
  end.

 (*Section DoubleProof.*)
  Variable w_digits : positive.
  Variable w_to_Z : w -> Z.


  Notation wB  := (base w_digits).
  Notation wwB := (base (ww_digits w_digits)).
  Notation "[| x |]" := (w_to_Z x)  (at level 0, x at level 99).
  Notation "[+| c |]" :=
   (interp_carry 1 wB w_to_Z c) (at level 0, c at level 99).
  Notation "[-| c |]" :=
   (interp_carry (-1) wB w_to_Z c) (at level 0, c at level 99).

  Notation "[[ x ]]" := (ww_to_Z w_digits w_to_Z x)(at level 0, x at level 99).
  Notation "[+[ c ]]" :=
   (interp_carry 1 wwB (ww_to_Z w_digits w_to_Z) c)
   (at level 0, c at level 99).
  Notation "[-[ c ]]" :=
   (interp_carry (-1) wwB (ww_to_Z w_digits w_to_Z) c)
   (at level 0, c at level 99).

  Variable spec_w_0   : [|w_0|] = 0.
  Variable spec_w_Bm1   : [|w_Bm1|] = wB - 1.
  Variable spec_ww_Bm1   : [[ww_Bm1]] = wwB - 1.
  Variable spec_to_Z  : forall x, 0 <= [|x|] < wB.
  Variable spec_w_WW : forall h l, [[w_WW h l]] = [|h|] * wB + [|l|].

  Variable spec_opp_c : forall x, [-|w_opp_c x|] = -[|x|].
  Variable spec_opp : forall x, [|w_opp x|] = (-[|x|]) mod wB.
  Variable spec_opp_carry : forall x, [|w_opp_carry x|] = wB - [|x|] - 1.

  Variable spec_pred_c : forall x, [-|w_pred_c x|] = [|x|] - 1.
  Variable spec_sub_c : forall x y, [-|w_sub_c x y|] = [|x|] - [|y|].
  Variable spec_sub_carry_c :
   forall x y, [-|w_sub_carry_c x y|] = [|x|] - [|y|] - 1.

  Variable spec_pred : forall x, [|w_pred x|] = ([|x|] - 1) mod wB.
  Variable spec_sub : forall x y, [|w_sub x y|] = ([|x|] - [|y|]) mod wB.
  Variable spec_sub_carry :
	 forall x y, [|w_sub_carry x y|] = ([|x|] - [|y|] - 1) mod wB.


  Lemma spec_ww_opp_c : forall x, [-[ww_opp_c x]] = -[[x]].
  Proof.
   destruct x as [ |xh xl];simpl. reflexivity.
   rewrite Z.opp_add_distr;generalize (spec_opp_c xl);destruct (w_opp_c xl)
   as [l|l];intros H;unfold interp_carry in H;rewrite <- H;
   rewrite <- Z.mul_opp_l.
   assert ([|l|] = 0).
    assert (H1:= spec_to_Z l);assert (H2 := spec_to_Z xl);omega.
   rewrite H0;generalize (spec_opp_c xh);destruct (w_opp_c xh)
   as [h|h];intros H1;unfold interp_carry in *;rewrite <- H1.
   assert ([|h|] = 0).
    assert (H3:= spec_to_Z h);assert (H2 := spec_to_Z xh);omega.
   rewrite H2;reflexivity.
   simpl ww_to_Z;rewrite wwB_wBwB;rewrite spec_w_0;ring.
   unfold interp_carry;simpl ww_to_Z;rewrite wwB_wBwB;rewrite spec_opp_carry;
   ring.
  Qed.

  Lemma spec_ww_opp : forall x, [[ww_opp x]] = (-[[x]]) mod wwB.
  Proof.
   destruct x as [ |xh xl];simpl. reflexivity.
   rewrite Z.opp_add_distr, <- Z.mul_opp_l.
   generalize (spec_opp_c xl);destruct (w_opp_c xl)
   as [l|l];intros H;unfold interp_carry in H;rewrite <- H;simpl ww_to_Z.
   rewrite spec_w_0;rewrite Z.add_0_r;rewrite wwB_wBwB.
   assert ([|l|] = 0).
    assert (H1:= spec_to_Z l);assert (H2 := spec_to_Z xl);omega.
   rewrite H0;rewrite Z.add_0_r; rewrite Z.pow_2_r;
    rewrite Zmult_mod_distr_r;try apply lt_0_wB.
   rewrite spec_opp;trivial.
   apply Zmod_unique with (q:= -1).
   exact (spec_ww_to_Z w_digits w_to_Z spec_to_Z (WW (w_opp_carry xh) l)).
   rewrite spec_opp_carry;rewrite wwB_wBwB;ring.
  Qed.

  Lemma spec_ww_opp_carry : forall x, [[ww_opp_carry x]] = wwB - [[x]] - 1.
  Proof.
   destruct x as [ |xh xl];simpl. rewrite spec_ww_Bm1;ring.
   rewrite spec_w_WW;simpl;repeat rewrite spec_opp_carry;rewrite wwB_wBwB;ring.
  Qed.

  Lemma spec_ww_pred_c : forall x, [-[ww_pred_c x]] = [[x]] - 1.
  Proof.
   destruct x as [ |xh xl];unfold ww_pred_c.
   unfold interp_carry;rewrite spec_ww_Bm1;simpl ww_to_Z;ring.
   simpl ww_to_Z;replace (([|xh|]*wB+[|xl|])-1) with ([|xh|]*wB+([|xl|]-1)).
   2:ring. generalize (spec_pred_c xl);destruct (w_pred_c xl) as [l|l];
   intros H;unfold interp_carry in H;rewrite <- H. simpl;apply spec_w_WW.
   rewrite Z.add_assoc;rewrite <- Z.mul_add_distr_r.
   assert ([|l|] = wB - 1).
     assert (H1:= spec_to_Z l);assert (H2 := spec_to_Z xl);omega.
   rewrite H0;change ([|xh|] + -1) with ([|xh|] - 1).
   generalize (spec_pred_c xh);destruct (w_pred_c xh) as [h|h];
   intros H1;unfold interp_carry in H1;rewrite <- H1.
   simpl;rewrite spec_w_Bm1;ring.
   assert ([|h|] = wB - 1).
     assert (H3:= spec_to_Z h);assert (H2 := spec_to_Z xh);omega.
   rewrite H2;unfold interp_carry;rewrite spec_ww_Bm1;rewrite wwB_wBwB;ring.
  Qed.

  Lemma spec_ww_sub_c : forall x y, [-[ww_sub_c x y]] = [[x]] - [[y]].
  Proof.
   destruct y as [ |yh yl];simpl. ring.
   destruct x as [ |xh xl];simpl. exact (spec_ww_opp_c (WW yh yl)).
   replace ([|xh|] * wB + [|xl|] - ([|yh|] * wB + [|yl|]))
   with (([|xh|]-[|yh|])*wB + ([|xl|]-[|yl|])). 2:ring.
   generalize (spec_sub_c xl yl);destruct (w_sub_c xl yl) as [l|l];intros H;
   unfold interp_carry in H;rewrite <- H.
   generalize (spec_sub_c xh yh);destruct (w_sub_c xh yh) as [h|h];intros H1;
   unfold interp_carry in H1;rewrite <- H1;unfold interp_carry;
   try rewrite spec_w_WW;simpl ww_to_Z;try rewrite wwB_wBwB;ring.
   rewrite Z.add_assoc;rewrite <- Z.mul_add_distr_r.
   change ([|xh|] - [|yh|] + -1) with ([|xh|] - [|yh|] - 1).
   generalize (spec_sub_carry_c xh yh);destruct (w_sub_carry_c xh yh) as [h|h];
   intros H1;unfold interp_carry in *;rewrite <- H1;simpl ww_to_Z;
   try rewrite wwB_wBwB;ring.
  Qed.

  Lemma spec_ww_sub_carry_c :
     forall x y, [-[ww_sub_carry_c x y]] = [[x]] - [[y]] - 1.
  Proof.
   destruct y as [ |yh yl];simpl.
   unfold Z.sub;simpl;rewrite Z.add_0_r;exact (spec_ww_pred_c x).
   destruct x as [ |xh xl].
   unfold interp_carry;rewrite spec_w_WW;simpl ww_to_Z;rewrite wwB_wBwB;
   repeat rewrite spec_opp_carry;ring.
   simpl ww_to_Z.
   replace ([|xh|] * wB + [|xl|] - ([|yh|] * wB + [|yl|]) - 1)
   with (([|xh|]-[|yh|])*wB + ([|xl|]-[|yl|]-1)). 2:ring.
   generalize (spec_sub_carry_c xl yl);destruct (w_sub_carry_c xl yl)
   as [l|l];intros H;unfold interp_carry in H;rewrite <- H.
   generalize (spec_sub_c xh yh);destruct (w_sub_c xh yh) as [h|h];intros H1;
   unfold interp_carry in H1;rewrite <- H1;unfold interp_carry;
   try rewrite spec_w_WW;simpl ww_to_Z;try rewrite wwB_wBwB;ring.
   rewrite Z.add_assoc;rewrite <- Z.mul_add_distr_r.
   change ([|xh|] - [|yh|] + -1) with ([|xh|] - [|yh|] - 1).
   generalize (spec_sub_carry_c xh yh);destruct (w_sub_carry_c xh yh) as [h|h];
   intros H1;unfold interp_carry in *;rewrite <- H1;try rewrite spec_w_WW;
   simpl ww_to_Z; try rewrite wwB_wBwB;ring.
  Qed.

  Lemma spec_ww_pred : forall x, [[ww_pred x]] = ([[x]] - 1) mod wwB.
  Proof.
   destruct x as [ |xh xl];simpl.
   apply Zmod_unique with (-1). apply spec_ww_to_Z;trivial.
   rewrite spec_ww_Bm1;ring.
   replace ([|xh|]*wB + [|xl|] - 1) with ([|xh|]*wB + ([|xl|] - 1)). 2:ring.
   generalize (spec_pred_c xl);destruct (w_pred_c xl) as [l|l];intro H;
   unfold interp_carry in H;rewrite <- H;simpl ww_to_Z.
   rewrite Zmod_small. apply spec_w_WW.
   exact (spec_ww_to_Z w_digits w_to_Z spec_to_Z (WW xh l)).
   rewrite Z.add_assoc;rewrite <- Z.mul_add_distr_r.
   change ([|xh|] + -1) with ([|xh|] - 1).
   assert ([|l|] = wB - 1).
    assert (H1:= spec_to_Z l);assert (H2:= spec_to_Z xl);omega.
   rewrite (mod_wwB w_digits w_to_Z);trivial.
   rewrite spec_pred;rewrite spec_w_Bm1;rewrite <- H0;trivial.
  Qed.

  Lemma spec_ww_sub : forall x y, [[ww_sub x y]] = ([[x]] - [[y]]) mod wwB.
  Proof.
   destruct y as [ |yh yl];simpl.
   ring_simplify ([[x]] - 0);rewrite Zmod_small;trivial. apply spec_ww_to_Z;trivial.
   destruct x as [ |xh xl];simpl. exact (spec_ww_opp (WW yh yl)).
   replace ([|xh|] * wB + [|xl|] - ([|yh|] * wB + [|yl|]))
   with (([|xh|] - [|yh|]) * wB + ([|xl|] - [|yl|])). 2:ring.
   generalize (spec_sub_c xl yl);destruct (w_sub_c xl yl)as[l|l];intros H;
   unfold interp_carry in H;rewrite <- H.
   rewrite spec_w_WW;rewrite (mod_wwB w_digits w_to_Z spec_to_Z).
   rewrite spec_sub;trivial.
   simpl ww_to_Z;rewrite Z.add_assoc;rewrite <- Z.mul_add_distr_r.
   rewrite (mod_wwB w_digits w_to_Z spec_to_Z);rewrite spec_sub_carry;trivial.
  Qed.

  Lemma spec_ww_sub_carry :
	 forall x y, [[ww_sub_carry x y]] = ([[x]] - [[y]] - 1) mod wwB.
  Proof.
   destruct y as [ |yh yl];simpl.
   ring_simplify ([[x]] - 0);exact (spec_ww_pred x).
   destruct x as [ |xh xl];simpl.
   apply Zmod_unique with (-1).
   apply spec_ww_to_Z;trivial.
   fold (ww_opp_carry (WW yh yl)).
   rewrite (spec_ww_opp_carry (WW yh yl));simpl ww_to_Z;ring.
   replace ([|xh|] * wB + [|xl|] - ([|yh|] * wB + [|yl|]) - 1)
   with (([|xh|] - [|yh|]) * wB + ([|xl|] - [|yl|] - 1)). 2:ring.
   generalize (spec_sub_carry_c xl yl);destruct (w_sub_carry_c xl yl)as[l|l];
   intros H;unfold interp_carry in H;rewrite <- H;rewrite spec_w_WW.
   rewrite (mod_wwB w_digits w_to_Z spec_to_Z);rewrite spec_sub;trivial.
   rewrite Z.add_assoc;rewrite <- Z.mul_add_distr_r.
   rewrite (mod_wwB w_digits w_to_Z spec_to_Z);rewrite spec_sub_carry;trivial.
  Qed.

(* End DoubleProof. *)

End DoubleSub.






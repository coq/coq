(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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

Section DoubleAdd.
 Variable w : Type.
 Variable w_0 : w.
 Variable w_1 : w.
 Variable w_WW : w -> w -> zn2z w.
 Variable w_W0 : w -> zn2z w.
 Variable ww_1 : zn2z w.
 Variable w_succ_c : w -> carry w.
 Variable w_add_c : w -> w -> carry w.
 Variable w_add_carry_c : w -> w -> carry w.
 Variable w_succ : w -> w.
 Variable w_add : w -> w -> w.
 Variable w_add_carry : w -> w -> w.

 Definition ww_succ_c x :=
  match x with
  | W0 => C0 ww_1
  | WW xh xl =>
    match w_succ_c xl with
    | C0 l => C0 (WW xh l)
    | C1 l =>
      match w_succ_c xh with
      | C0 h => C0 (WW h w_0)
      | C1 h => C1 W0
      end
    end
  end.

 Definition ww_succ x :=
  match x with
  | W0 => ww_1
  | WW xh xl =>
    match w_succ_c xl with
    | C0 l => WW xh l
    | C1 l => w_W0 (w_succ xh)
    end
  end.

 Definition ww_add_c x y :=
  match x, y with
  | W0, _ => C0 y
  | _, W0 => C0 x
  | WW xh xl, WW yh yl =>
    match w_add_c xl yl with
    | C0 l =>
      match w_add_c xh yh with
      | C0 h => C0 (WW h l)
      | C1 h => C1 (w_WW h l)
      end
    | C1 l =>
      match w_add_carry_c xh yh with
      | C0 h => C0 (WW h l)
      | C1 h => C1 (w_WW h l)
      end
    end
  end.

 Variable R : Type.
 Variable f0 f1 : zn2z w -> R.

 Definition ww_add_c_cont x y :=
  match x, y with
  | W0, _ => f0 y
  | _, W0 => f0 x
  | WW xh xl, WW yh yl =>
    match w_add_c xl yl with
    | C0 l =>
      match w_add_c xh yh with
      | C0 h => f0 (WW h l)
      | C1 h => f1 (w_WW h l)
      end
    | C1 l =>
      match w_add_carry_c xh yh with
      | C0 h => f0 (WW h l)
      | C1 h => f1 (w_WW h l)
      end
    end
  end.

 (* ww_add et ww_add_carry conserve la forme normale s'il n'y a pas
    de debordement *)
 Definition ww_add x y :=
  match x, y with
  | W0, _ => y
  | _, W0 => x
  | WW xh xl, WW yh yl =>
    match w_add_c xl yl with
    | C0 l => WW (w_add xh yh) l
    | C1 l => WW (w_add_carry xh yh) l
    end
  end.

 Definition ww_add_carry_c x y :=
  match x, y with
  | W0, W0 => C0 ww_1
  | W0, WW yh yl => ww_succ_c (WW yh yl)
  | WW xh xl, W0 => ww_succ_c (WW xh xl)
  | WW xh xl, WW yh yl =>
    match w_add_carry_c xl yl with
    | C0 l =>
      match w_add_c xh yh with
      | C0 h => C0 (WW h l)
      | C1 h => C1 (WW h l)
      end
    | C1 l =>
      match w_add_carry_c xh yh with
      | C0 h => C0 (WW h l)
      | C1 h => C1 (w_WW h l)
      end
    end
  end.

 Definition ww_add_carry x y :=
  match x, y with
  | W0, W0 => ww_1
  | W0, WW yh yl => ww_succ (WW yh yl)
  | WW xh xl, W0 => ww_succ (WW xh xl)
  | WW xh xl, WW yh yl =>
    match w_add_carry_c xl yl with
    | C0 l => WW (w_add xh yh) l
    | C1 l => WW (w_add_carry xh yh) l
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
  Variable spec_w_1   : [|w_1|] = 1.
  Variable spec_ww_1   : [[ww_1]] = 1.
  Variable spec_to_Z  : forall x, 0 <= [|x|] < wB.
  Variable spec_w_WW : forall h l, [[w_WW h l]] = [|h|] * wB + [|l|].
  Variable spec_w_W0 : forall h, [[w_W0 h]] = [|h|] * wB.
  Variable spec_w_succ_c : forall x, [+|w_succ_c x|] = [|x|] + 1.
  Variable spec_w_add_c  : forall x y, [+|w_add_c x y|] = [|x|] + [|y|].
  Variable spec_w_add_carry_c :
         forall x y, [+|w_add_carry_c x y|] = [|x|] + [|y|] + 1.
  Variable spec_w_succ : forall x, [|w_succ x|] = ([|x|] + 1) mod wB.
  Variable spec_w_add : forall x y, [|w_add x y|] = ([|x|] + [|y|]) mod wB.
  Variable spec_w_add_carry :
	 forall x y, [|w_add_carry x y|] = ([|x|] + [|y|] + 1) mod wB.

  Lemma spec_ww_succ_c : forall x, [+[ww_succ_c x]] = [[x]] + 1.
  Proof.
   destruct x as [ |xh xl];simpl. apply spec_ww_1.
   generalize (spec_w_succ_c xl);destruct (w_succ_c xl) as [l|l];
    intro H;unfold interp_carry in H. simpl;rewrite H;ring.
   rewrite <- Z.add_assoc;rewrite <- H;rewrite Z.mul_1_l.
   assert ([|l|] = 0). generalize (spec_to_Z xl)(spec_to_Z l);omega.
   rewrite H0;generalize (spec_w_succ_c xh);destruct (w_succ_c xh) as [h|h];
    intro H1;unfold interp_carry in H1.
   simpl;rewrite H1;rewrite spec_w_0;ring.
   unfold interp_carry;simpl ww_to_Z;rewrite wwB_wBwB.
   assert ([|xh|] = wB - 1). generalize (spec_to_Z xh)(spec_to_Z h);omega.
   rewrite H2;ring.
  Qed.

  Lemma spec_ww_add_c  : forall x y, [+[ww_add_c x y]] = [[x]] + [[y]].
  Proof.
   destruct x as [ |xh xl];trivial.
   destruct y as [ |yh yl]. rewrite Z.add_0_r;trivial.
   simpl. replace ([|xh|] * wB + [|xl|] + ([|yh|] * wB + [|yl|]))
   with (([|xh|]+[|yh|])*wB + ([|xl|]+[|yl|])). 2:ring.
   generalize (spec_w_add_c xl yl);destruct (w_add_c xl yl) as [l|l];
    intros H;unfold interp_carry in H;rewrite <- H.
   generalize (spec_w_add_c xh yh);destruct (w_add_c xh yh) as [h|h];
    intros H1;unfold interp_carry in *;rewrite <- H1. trivial.
   repeat rewrite Z.mul_1_l;rewrite spec_w_WW;rewrite wwB_wBwB; ring.
   rewrite Z.add_assoc;rewrite <- Z.mul_add_distr_r.
   generalize (spec_w_add_carry_c xh yh);destruct (w_add_carry_c xh yh)
    as [h|h]; intros H1;unfold interp_carry in *;rewrite <- H1.
   simpl;ring.
   repeat rewrite Z.mul_1_l;rewrite wwB_wBwB;rewrite spec_w_WW;ring.
  Qed.

  Section Cont.
   Variable P : zn2z w -> zn2z w -> R -> Prop.
   Variable x y : zn2z w.
   Variable spec_f0 : forall r, [[r]] = [[x]] + [[y]] -> P x y (f0 r).
   Variable spec_f1 : forall r, wwB + [[r]] = [[x]] + [[y]] -> P x y (f1 r).

   Lemma spec_ww_add_c_cont  : P x y (ww_add_c_cont x y).
   Proof.
    destruct x as [ |xh xl];trivial.
    apply spec_f0;trivial.
    destruct y as [ |yh yl].
    apply spec_f0;rewrite Z.add_0_r;trivial.
    simpl.
    generalize (spec_w_add_c xl yl);destruct (w_add_c xl yl) as [l|l];
     intros H;unfold interp_carry in H.
    generalize (spec_w_add_c xh yh);destruct (w_add_c xh yh) as [h|h];
     intros H1;unfold interp_carry in *.
    apply spec_f0. simpl;rewrite H;rewrite H1;ring.
    apply spec_f1. simpl;rewrite spec_w_WW;rewrite H.
    rewrite Z.add_assoc;rewrite wwB_wBwB. rewrite Z.pow_2_r; rewrite <- Z.mul_add_distr_r.
    rewrite Z.mul_1_l in H1;rewrite H1;ring.
    generalize (spec_w_add_carry_c xh yh);destruct (w_add_carry_c xh yh)
     as [h|h]; intros H1;unfold interp_carry in *.
    apply spec_f0;simpl;rewrite H1. rewrite Z.mul_add_distr_r.
    rewrite <- Z.add_assoc;rewrite H;ring.
    apply spec_f1. rewrite spec_w_WW;rewrite wwB_wBwB.
    rewrite Z.add_assoc; rewrite Z.pow_2_r; rewrite <- Z.mul_add_distr_r.
    rewrite Z.mul_1_l in H1;rewrite H1. rewrite Z.mul_add_distr_r.
    rewrite <- Z.add_assoc;rewrite H; simpl; ring.
   Qed.

  End Cont.

  Lemma spec_ww_add_carry_c :
         forall x y, [+[ww_add_carry_c x y]] = [[x]] + [[y]] + 1.
  Proof.
   destruct x as [ |xh xl];intro y.
   exact (spec_ww_succ_c y).
   destruct y as [ |yh yl].
   rewrite Z.add_0_r;exact (spec_ww_succ_c (WW xh xl)).
   simpl; replace ([|xh|] * wB + [|xl|] + ([|yh|] * wB + [|yl|]) + 1)
   with (([|xh|]+[|yh|])*wB + ([|xl|]+[|yl|]+1)). 2:ring.
   generalize (spec_w_add_carry_c xl yl);destruct (w_add_carry_c xl yl)
    as [l|l];intros H;unfold interp_carry in H;rewrite <- H.
   generalize (spec_w_add_c xh yh);destruct (w_add_c xh yh) as [h|h];
    intros H1;unfold interp_carry in H1;rewrite <- H1. trivial.
   unfold interp_carry;repeat rewrite Z.mul_1_l;simpl;rewrite wwB_wBwB;ring.
   rewrite Z.add_assoc;rewrite <- Z.mul_add_distr_r.
   generalize (spec_w_add_carry_c xh yh);destruct (w_add_carry_c xh yh)
    as [h|h];intros H1;unfold interp_carry in H1;rewrite <- H1. trivial.
   unfold interp_carry;rewrite spec_w_WW;
   repeat rewrite Z.mul_1_l;simpl;rewrite wwB_wBwB;ring.
  Qed.

  Lemma spec_ww_succ : forall x, [[ww_succ x]] = ([[x]] + 1) mod wwB.
  Proof.
   destruct x as [ |xh xl];simpl.
   rewrite spec_ww_1;rewrite Zmod_small;trivial.
   split;[intro;discriminate|apply wwB_pos].
   rewrite <- Z.add_assoc;generalize (spec_w_succ_c xl);
   destruct (w_succ_c xl) as[l|l];intro H;unfold interp_carry in H;rewrite <-H.
   rewrite Zmod_small;trivial.
   rewrite wwB_wBwB;apply beta_mult;apply spec_to_Z.
   assert ([|l|] = 0). clear spec_ww_1 spec_w_1 spec_w_0.
    assert (H1:= spec_to_Z l); assert (H2:= spec_to_Z xl); omega.
   rewrite H0;rewrite Z.add_0_r;rewrite <- Z.mul_add_distr_r;rewrite wwB_wBwB.
   rewrite Z.pow_2_r; rewrite Zmult_mod_distr_r;try apply lt_0_wB.
   rewrite spec_w_W0;rewrite spec_w_succ;trivial.
  Qed.

  Lemma spec_ww_add : forall x y, [[ww_add x y]] = ([[x]] + [[y]]) mod wwB.
  Proof.
   destruct x as [ |xh xl];intros y.
   rewrite Zmod_small;trivial. apply spec_ww_to_Z;trivial.
   destruct y as [ |yh yl].
   change [[W0]] with 0;rewrite Z.add_0_r.
   rewrite Zmod_small;trivial.
    exact (spec_ww_to_Z w_digits w_to_Z spec_to_Z (WW xh xl)).
   simpl. replace ([|xh|] * wB + [|xl|] + ([|yh|] * wB + [|yl|]))
   with (([|xh|]+[|yh|])*wB + ([|xl|]+[|yl|])). 2:ring.
   generalize (spec_w_add_c xl yl);destruct (w_add_c xl yl) as [l|l];
   unfold interp_carry;intros H;simpl;rewrite <- H.
   rewrite (mod_wwB w_digits w_to_Z spec_to_Z);rewrite spec_w_add;trivial.
   rewrite Z.add_assoc;rewrite <- Z.mul_add_distr_r.
   rewrite(mod_wwB w_digits w_to_Z spec_to_Z);rewrite spec_w_add_carry;trivial.
  Qed.

  Lemma spec_ww_add_carry :
	 forall x y, [[ww_add_carry x y]] = ([[x]] + [[y]] + 1) mod wwB.
  Proof.
   destruct x as [ |xh xl];intros y.
   exact (spec_ww_succ y).
   destruct y as [ |yh yl].
   change [[W0]] with 0;rewrite Z.add_0_r. exact (spec_ww_succ (WW xh xl)).
   simpl;replace ([|xh|] * wB + [|xl|] + ([|yh|] * wB + [|yl|]) + 1)
   with (([|xh|]+[|yh|])*wB + ([|xl|]+[|yl|]+1)). 2:ring.
   generalize (spec_w_add_carry_c xl yl);destruct (w_add_carry_c xl yl)
   as [l|l];unfold interp_carry;intros H;rewrite <- H;simpl ww_to_Z.
   rewrite(mod_wwB w_digits w_to_Z spec_to_Z);rewrite spec_w_add;trivial.
   rewrite Z.add_assoc;rewrite <- Z.mul_add_distr_r.
   rewrite(mod_wwB w_digits w_to_Z spec_to_Z);rewrite spec_w_add_carry;trivial.
  Qed.

(* End DoubleProof. *)
End DoubleAdd.

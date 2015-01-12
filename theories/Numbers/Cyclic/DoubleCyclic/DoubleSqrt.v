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

Section DoubleSqrt.
 Variable w              : Type.
 Variable w_is_even      : w -> bool.
 Variable w_compare      : w -> w -> comparison.
 Variable w_0            : w.
 Variable w_1            : w.
 Variable w_Bm1          : w.
 Variable w_WW           : w -> w -> zn2z w.
 Variable w_W0           : w -> zn2z w.
 Variable w_0W           : w -> zn2z w.
 Variable w_sub          : w -> w -> w.
 Variable w_sub_c        : w -> w -> carry w.
 Variable w_square_c     : w -> zn2z w.
 Variable w_div21        : w -> w -> w -> w * w.
 Variable w_add_mul_div  : w -> w -> w -> w.
 Variable w_digits       : positive.
 Variable w_zdigits      : w.
 Variable ww_zdigits     : zn2z w.
 Variable w_add_c        : w -> w -> carry w.
 Variable w_sqrt2        : w -> w -> w * carry w.
 Variable w_pred         : w -> w.
 Variable ww_pred_c      : zn2z w -> carry (zn2z w).
 Variable ww_pred        : zn2z w -> zn2z w.
 Variable ww_add_c       : zn2z w -> zn2z w -> carry (zn2z w).
 Variable ww_add         : zn2z w -> zn2z w -> zn2z w.
 Variable ww_sub_c       : zn2z w -> zn2z w -> carry (zn2z w).
 Variable ww_add_mul_div : zn2z w -> zn2z w -> zn2z w -> zn2z w.
 Variable ww_head0       : zn2z w -> zn2z w.
 Variable ww_compare     : zn2z w -> zn2z w -> comparison.
 Variable low            : zn2z w -> w.

 Let wwBm1 := ww_Bm1 w_Bm1.

 Definition ww_is_even x :=
   match x with
   | W0 => true
   | WW xh xl => w_is_even xl
   end.

 Let w_div21c x y z :=
   match w_compare x z with
   | Eq =>
      match w_compare y z with
        Eq => (C1 w_1, w_0)
      | Gt => (C1 w_1, w_sub y z)
      | Lt => (C1 w_0, y)
      end
   | Gt =>
      let x1 := w_sub x z in
      let (q, r) := w_div21 x1 y z in
        (C1 q, r)
   | Lt =>
      let (q, r) := w_div21 x y z in
        (C0 q, r)
   end.

 Let w_div2s x y s :=
  match x with
   C1 x1 =>
     let x2 := w_sub x1 s in
     let (q, r) := w_div21c x2 y s in
     match q with
       C0 q1 =>
         if w_is_even q1 then
          (C0 (w_add_mul_div (w_pred w_zdigits) w_1 q1), C0 r)
         else
          (C0 (w_add_mul_div (w_pred w_zdigits) w_1 q1), w_add_c r s)
     | C1 q1 =>
         if w_is_even q1 then
          (C1 (w_add_mul_div (w_pred w_zdigits) w_0 q1), C0 r)
         else
          (C1 (w_add_mul_div (w_pred w_zdigits) w_0 q1), w_add_c r s)
     end
  | C0 x1 =>
     let (q, r) := w_div21c x1 y s in
     match q with
       C0 q1 =>
         if w_is_even q1 then
          (C0 (w_add_mul_div (w_pred w_zdigits) w_0 q1), C0 r)
         else
          (C0 (w_add_mul_div (w_pred w_zdigits) w_0 q1), w_add_c r s)
     | C1 q1 =>
         if w_is_even q1 then
          (C0 (w_add_mul_div (w_pred w_zdigits) w_1 q1), C0 r)
         else
          (C0 (w_add_mul_div (w_pred w_zdigits) w_1 q1), w_add_c r s)
     end
  end.

 Definition split x :=
 match x with
  | W0 => (w_0,w_0)
  | WW h l => (h,l)
  end.

 Definition ww_sqrt2 x y :=
   let (x1, x2) := split x in
   let (y1, y2) := split y in
   let ( q, r)  := w_sqrt2 x1 x2 in
   let (q1, r1) := w_div2s r y1 q in
   match q1 with
     C0 q1 =>
      let q2 := w_square_c q1 in
      let a  := WW q q1 in
        match r1 with
          C1 r2 =>
           match ww_sub_c (WW r2 y2) q2 with
             C0 r3 => (a, C1 r3)
           | C1 r3 => (a, C0 r3)
           end
        | C0 r2 =>
           match ww_sub_c (WW r2 y2) q2 with
             C0 r3 => (a, C0 r3)
           | C1 r3 =>
              let a2 := ww_add_mul_div (w_0W w_1) a W0 in
              match ww_pred_c a2 with
                C0 a3 =>
                  (ww_pred a, ww_add_c a3 r3)
              | C1 a3 =>
                  (ww_pred a, C0 (ww_add a3 r3))
              end
            end
         end
   | C1 q1 =>
         let a1 := WW q w_Bm1 in
         let a2 := ww_add_mul_div (w_0W w_1) a1 wwBm1 in
            (a1, ww_add_c a2 y)
   end.

 Definition ww_is_zero x :=
  match ww_compare W0 x with
   Eq => true
  | _ => false
  end.

 Definition ww_head1 x :=
   let p := ww_head0 x in
   if (ww_is_even p) then p else ww_pred p.

 Definition ww_sqrt x :=
   if (ww_is_zero x) then W0
   else
    let p := ww_head1 x in
    match ww_compare p W0 with
    | Gt =>
        match ww_add_mul_div p x W0 with
         W0 => W0
       | WW x1 x2 =>
          let (r, _) := w_sqrt2 x1 x2 in
            WW w_0 (w_add_mul_div
                     (w_sub w_zdigits
                     (low (ww_add_mul_div (ww_pred ww_zdigits)
                              W0 p))) w_0 r)
        end
     | _ =>
        match x with
          W0 => W0
        | WW x1 x2 => WW w_0 (fst (w_sqrt2 x1 x2))
        end
    end.


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

  Notation "[|| x ||]" :=
    (zn2z_to_Z wwB (ww_to_Z w_digits w_to_Z) x)  (at level 0, x at level 99).

  Notation "[! n | x !]" := (double_to_Z w_digits w_to_Z n x)
    (at level 0, x at level 99).

  Variable spec_w_0   : [|w_0|] = 0.
  Variable spec_w_1   : [|w_1|] = 1.
  Variable spec_w_Bm1 : [|w_Bm1|] = wB - 1.
  Variable spec_w_zdigits : [|w_zdigits|] = Zpos w_digits.
  Variable spec_more_than_1_digit: 1 < Zpos w_digits.

  Variable spec_ww_zdigits : [[ww_zdigits]] = Zpos (xO w_digits).
  Variable spec_to_Z  : forall x, 0 <= [|x|] < wB.
  Variable spec_to_w_Z  : forall x, 0 <= [[x]] < wwB.

  Variable spec_w_WW : forall h l, [[w_WW h l]] = [|h|] * wB + [|l|].
  Variable spec_w_W0 : forall h, [[w_W0 h]] = [|h|] * wB.
  Variable spec_w_0W : forall l, [[w_0W l]] = [|l|].
  Variable spec_w_is_even : forall x,
      if w_is_even x then [|x|] mod 2 = 0 else [|x|] mod 2 = 1.
  Variable spec_w_compare : forall x y,
       w_compare x y = Z.compare [|x|] [|y|].
 Variable spec_w_sub : forall x y, [|w_sub x y|] = ([|x|] - [|y|]) mod wB.
 Variable spec_w_square_c : forall x, [[ w_square_c x]] = [|x|] * [|x|].
 Variable spec_w_div21 : forall a1 a2 b,
     wB/2 <= [|b|] ->
     [|a1|] < [|b|] ->
     let (q,r) := w_div21 a1 a2 b in
     [|a1|] *wB+ [|a2|] = [|q|] * [|b|] + [|r|] /\
     0 <= [|r|] < [|b|].
 Variable spec_w_add_mul_div : forall x y p,
        [|p|] <= Zpos w_digits ->
       [| w_add_mul_div p x y |] =
         ([|x|] * (2 ^ [|p|]) +
          [|y|] / (Z.pow 2 ((Zpos w_digits) - [|p|]))) mod wB.
 Variable spec_ww_add_mul_div : forall x y p,
       [[p]] <= Zpos (xO w_digits) ->
       [[ ww_add_mul_div p x y ]] =
         ([[x]] * (2^ [[p]]) +
          [[y]] / (2^ (Zpos (xO w_digits) - [[p]]))) mod wwB.
 Variable spec_w_add_c  : forall x y, [+|w_add_c x y|] = [|x|] + [|y|].
 Variable spec_ww_add : forall x y, [[ww_add x y]] = ([[x]] + [[y]]) mod wwB.
 Variable spec_w_sqrt2 : forall x y,
       wB/ 4 <= [|x|] ->
       let (s,r) := w_sqrt2 x y in
          [[WW x y]] = [|s|] ^ 2 + [+|r|] /\
          [+|r|] <= 2 * [|s|].
 Variable spec_ww_sub_c : forall x y, [-[ww_sub_c x y]] = [[x]] - [[y]].
 Variable spec_ww_pred_c : forall x, [-[ww_pred_c x]] = [[x]] - 1.
 Variable spec_pred : forall x, [|w_pred x|] = ([|x|] - 1) mod wB.
 Variable spec_ww_pred : forall x, [[ww_pred x]] = ([[x]] - 1) mod wwB.
 Variable spec_ww_add_c  : forall x y, [+[ww_add_c x y]] = [[x]] + [[y]].
 Variable spec_ww_compare : forall x y,
    ww_compare x y = Z.compare [[x]] [[y]].
 Variable spec_ww_head0  : forall x,  0 < [[x]] ->
	 wwB/ 2 <= 2 ^ [[ww_head0 x]] * [[x]] < wwB.
 Variable spec_low: forall x, [|low x|] = [[x]] mod wB.

 Let spec_ww_Bm1 : [[wwBm1]] = wwB - 1.
 Proof. refine (spec_ww_Bm1 w_Bm1 w_digits w_to_Z _);auto. Qed.

 Hint Rewrite spec_w_0 spec_w_1 spec_w_WW spec_w_sub
   spec_w_add_mul_div spec_ww_Bm1 spec_w_add_c : w_rewrite.

 Lemma spec_ww_is_even : forall x,
      if ww_is_even x then [[x]] mod 2 = 0 else [[x]] mod 2 = 1.
clear spec_more_than_1_digit.
intros x; case x; simpl ww_is_even.
 reflexivity.
 simpl.
 intros w1 w2; simpl.
 unfold base.
 rewrite Zplus_mod; auto with zarith.
 rewrite (fun x y => (Zdivide_mod (x * y))); auto with zarith.
 rewrite Z.add_0_l; rewrite Zmod_mod; auto with zarith.
 apply spec_w_is_even; auto with zarith.
 apply Z.divide_mul_r; apply Zpower_divide; auto with zarith.
 Qed.


 Theorem  spec_w_div21c : forall a1 a2 b,
     wB/2 <= [|b|] ->
     let (q,r) := w_div21c a1 a2 b in
     [|a1|] * wB + [|a2|] = [+|q|] *  [|b|] + [|r|] /\ 0 <= [|r|] < [|b|].
 intros a1 a2 b Hb; unfold w_div21c.
 assert (H: 0 < [|b|]); auto with zarith.
 assert (U := wB_pos w_digits).
 apply Z.lt_le_trans with (2 := Hb); auto with zarith.
 apply Z.lt_le_trans with 1; auto with zarith.
 apply Zdiv_le_lower_bound; auto with zarith.
 rewrite !spec_w_compare. repeat case Z.compare_spec.
 intros H1 H2; split.
 unfold interp_carry; autorewrite with w_rewrite rm10; auto with zarith.
 rewrite H1; rewrite H2; ring.
 autorewrite with w_rewrite; auto with zarith.
 intros H1 H2; split.
 unfold interp_carry; autorewrite with w_rewrite rm10; auto with zarith.
 rewrite H2; ring.
 destruct (spec_to_Z a2);auto with zarith.
 intros H1 H2; split.
 unfold interp_carry; autorewrite with w_rewrite rm10; auto with zarith.
 rewrite H2; rewrite Zmod_small; auto with zarith.
 ring.
 destruct (spec_to_Z a2);auto with zarith.
 rewrite spec_w_sub; auto with zarith.
 destruct (spec_to_Z a2) as [H3 H4];auto with zarith.
 rewrite Zmod_small; auto with zarith.
 split; auto with zarith.
 assert ([|a2|] < 2 * [|b|]); auto with zarith.
 apply Z.lt_le_trans with (2 * (wB / 2)); auto with zarith.
 rewrite wB_div_2; auto.
 intros H1.
 match goal with |- context[w_div21 ?y ?z ?t] =>
   generalize (@spec_w_div21 y z t Hb H1);
   case (w_div21 y z t); simpl; autorewrite with w_rewrite;
   auto
 end.
 intros H1.
 assert (H2: [|w_sub a1 b|] < [|b|]).
 rewrite spec_w_sub; auto with zarith.
 rewrite Zmod_small; auto with zarith.
 assert ([|a1|] < 2 * [|b|]); auto with zarith.
 apply Z.lt_le_trans with (2 * (wB / 2)); auto with zarith.
 rewrite wB_div_2; auto.
 destruct (spec_to_Z a1);auto with zarith.
 destruct (spec_to_Z a1);auto with zarith.
 match goal with |- context[w_div21 ?y ?z ?t] =>
   generalize (@spec_w_div21 y z t Hb H2);
   case (w_div21 y z t); autorewrite with w_rewrite;
   auto
 end.
 intros w0 w1; replace [+|C1 w0|] with (wB + [|w0|]).
 rewrite Zmod_small; auto with zarith.
 intros (H3, H4); split; auto.
 rewrite Z.mul_add_distr_r.
 rewrite <- Z.add_assoc; rewrite <- H3; ring.
 split; auto with zarith.
 assert ([|a1|] < 2 * [|b|]); auto with zarith.
 apply Z.lt_le_trans with (2 * (wB / 2)); auto with zarith.
 rewrite wB_div_2; auto.
 destruct (spec_to_Z a1);auto with zarith.
 destruct (spec_to_Z a1);auto with zarith.
 simpl; case wB; auto.
 Qed.

 Theorem C0_id: forall p, [+|C0 p|] = [|p|].
 intros p; simpl; auto.
 Qed.

 Theorem add_mult_div_2: forall w,
    [|w_add_mul_div (w_pred w_zdigits) w_0 w|] = [|w|] / 2.
 intros w1.
 assert (Hp: [|w_pred w_zdigits|] = Zpos w_digits - 1).
   rewrite spec_pred; rewrite spec_w_zdigits.
   rewrite Zmod_small; auto with zarith.
   split; auto with zarith.
   apply Z.lt_le_trans with (Zpos w_digits); auto with zarith.
   unfold base; apply Zpower2_le_lin; auto with zarith.
 rewrite spec_w_add_mul_div; auto with zarith.
 autorewrite with w_rewrite rm10.
 match goal with |- context[?X - ?Y] =>
  replace (X - Y) with 1
 end.
 rewrite Z.pow_1_r; rewrite Zmod_small; auto with zarith.
 destruct (spec_to_Z w1) as [H1 H2];auto with zarith.
 split; auto with zarith.
 apply Zdiv_lt_upper_bound; auto with zarith.
 rewrite Hp; ring.
 Qed.

 Theorem add_mult_div_2_plus_1: forall w,
    [|w_add_mul_div (w_pred w_zdigits) w_1 w|] =
      [|w|] / 2 + 2 ^ Zpos (w_digits - 1).
 intros w1.
 assert (Hp: [|w_pred w_zdigits|] = Zpos w_digits - 1).
   rewrite spec_pred; rewrite spec_w_zdigits.
   rewrite Zmod_small; auto with zarith.
   split; auto with zarith.
   apply Z.lt_le_trans with (Zpos w_digits); auto with zarith.
   unfold base; apply Zpower2_le_lin; auto with zarith.
 autorewrite with w_rewrite rm10; auto with zarith.
 match goal with |- context[?X - ?Y] =>
  replace (X - Y) with 1
 end; rewrite Hp; try ring.
 rewrite Pos2Z.inj_sub_max; auto with zarith.
 rewrite Z.max_r; auto with zarith.
 rewrite Z.pow_1_r; rewrite Zmod_small; auto with zarith.
 destruct (spec_to_Z w1) as [H1 H2];auto with zarith.
 split; auto with zarith.
 unfold base.
 match goal with |- _ < _ ^ ?X =>
 assert (tmp: forall p, 1 + (p - 1) = p); auto with zarith;
  rewrite <- (tmp X); clear tmp
 end.
 rewrite Zpower_exp; try rewrite Z.pow_1_r; auto with zarith.
 assert (tmp: forall p, 1 + (p -1) - 1 = p - 1); auto with zarith;
  rewrite tmp; clear tmp; auto with zarith.
 match goal with |- ?X + ?Y < _ =>
 assert (Y < X); auto with zarith
 end.
 apply Zdiv_lt_upper_bound; auto with zarith.
 pattern 2 at 2; rewrite <- Z.pow_1_r; rewrite <- Zpower_exp;
  auto with zarith.
 assert (tmp: forall p, (p - 1) + 1 = p); auto with zarith;
  rewrite tmp; clear tmp; auto with zarith.
 Qed.

 Theorem add_mult_mult_2: forall w,
    [|w_add_mul_div w_1 w w_0|] = 2 * [|w|] mod wB.
 intros w1.
 autorewrite with w_rewrite rm10; auto with zarith.
 rewrite Z.pow_1_r; auto with zarith.
 rewrite Z.mul_comm; auto.
 Qed.

 Theorem ww_add_mult_mult_2: forall w,
    [[ww_add_mul_div (w_0W w_1) w W0]] = 2 * [[w]] mod wwB.
 intros w1.
 rewrite spec_ww_add_mul_div; auto with zarith.
 autorewrite with w_rewrite rm10.
 rewrite spec_w_0W; rewrite spec_w_1.
 rewrite Z.pow_1_r; auto with zarith.
 rewrite Z.mul_comm; auto.
 rewrite spec_w_0W; rewrite spec_w_1; auto with zarith.
 red; simpl; intros; discriminate.
 Qed.

 Theorem ww_add_mult_mult_2_plus_1: forall w,
    [[ww_add_mul_div (w_0W w_1) w wwBm1]] =
      (2 * [[w]] + 1) mod wwB.
 intros w1.
 rewrite spec_ww_add_mul_div; auto with zarith.
 rewrite spec_w_0W; rewrite spec_w_1; auto with zarith.
 rewrite Z.pow_1_r; auto with zarith.
 f_equal; auto.
 rewrite Z.mul_comm; f_equal; auto.
 autorewrite with w_rewrite rm10.
 unfold ww_digits, base.
 symmetry; apply Zdiv_unique with (r := 2 ^ (Zpos (ww_digits w_digits) - 1) -1);
  auto with zarith.
 unfold ww_digits; split; auto with zarith.
 match goal with  |- 0 <= ?X - 1 =>
   assert (0 < X); auto with zarith
 end.
 apply Z.pow_pos_nonneg; auto with zarith.
 match goal with  |- 0 <= ?X - 1 =>
   assert (0 < X); auto with zarith; red; reflexivity
 end.
 unfold ww_digits; autorewrite with rm10.
 assert (tmp: forall p q r, p + (q - r) = p + q - r); auto with zarith;
  rewrite tmp; clear tmp.
 assert (tmp: forall p, p + p = 2 * p); auto with zarith;
  rewrite tmp; clear tmp.
 f_equal; auto.
 pattern 2 at 2; rewrite <- Z.pow_1_r; rewrite <- Zpower_exp;
  auto with zarith.
 assert (tmp: forall p, 1 + (p - 1) = p); auto with zarith;
  rewrite tmp; clear tmp; auto.
 match goal with  |- ?X - 1 >= 0 =>
   assert (0 < X); auto with zarith; red; reflexivity
 end.
 rewrite spec_w_0W; rewrite spec_w_1; auto with zarith.
 red; simpl; intros; discriminate.
 Qed.

 Theorem Zplus_mod_one: forall a1 b1, 0 < b1 -> (a1 + b1) mod b1 = a1 mod b1.
 intros a1 b1 H; rewrite Zplus_mod; auto with zarith.
 rewrite Z_mod_same; try rewrite Z.add_0_r; auto with zarith.
 apply Zmod_mod; auto.
 Qed.

 Lemma C1_plus_wB: forall x, [+|C1 x|] = wB + [|x|].
 unfold interp_carry; auto with zarith.
 Qed.

 Theorem  spec_w_div2s : forall a1 a2 b,
     wB/2 <= [|b|] -> [+|a1|] <= 2 * [|b|] ->
     let (q,r) := w_div2s a1 a2 b in
     [+|a1|] * wB + [|a2|] = [+|q|] *  (2 * [|b|]) + [+|r|] /\ 0 <= [+|r|] < 2 * [|b|].
 intros a1 a2 b H.
 assert (HH: 0 < [|b|]); auto with zarith.
 assert (U := wB_pos w_digits).
 apply Z.lt_le_trans with (2 := H); auto with zarith.
 apply Z.lt_le_trans with 1; auto with zarith.
 apply Zdiv_le_lower_bound; auto with zarith.
 unfold w_div2s; case a1; intros w0 H0.
 match goal with |- context[w_div21c ?y ?z ?t] =>
   generalize (@spec_w_div21c y z t H);
   case (w_div21c y z t); autorewrite with w_rewrite;
   auto
 end.
 intros c w1; case c.
 simpl interp_carry; intros w2 (Hw1, Hw2).
 match goal with |- context[w_is_even ?y] =>
   generalize (spec_w_is_even y);
   case (w_is_even y)
 end.
 repeat rewrite C0_id.
 rewrite add_mult_div_2.
 intros H1; split; auto with zarith.
 rewrite Hw1.
 pattern [|w2|] at 1; rewrite (Z_div_mod_eq [|w2|] 2);
  auto with zarith.
 rewrite H1; ring.
 repeat rewrite C0_id.
 rewrite add_mult_div_2.
 rewrite spec_w_add_c; auto with zarith.
 intros H1; split; auto with zarith.
 rewrite Hw1.
 pattern [|w2|] at 1; rewrite (Z_div_mod_eq [|w2|] 2);
  auto with zarith.
 rewrite H1; ring.
 intros w2; rewrite C1_plus_wB.
 intros (Hw1, Hw2).
 match goal with |- context[w_is_even ?y] =>
   generalize (spec_w_is_even y);
   case (w_is_even y)
 end.
 repeat rewrite C0_id.
 intros H1; split; auto with zarith.
 rewrite Hw1.
 pattern [|w2|] at 1; rewrite (Z_div_mod_eq [|w2|] 2);
  auto with zarith.
 rewrite H1.
 repeat rewrite C0_id.
 rewrite add_mult_div_2_plus_1; unfold base.
 match goal with |- context[_ ^ ?X] =>
 assert (tmp: forall p, 1 + (p - 1) = p); auto with zarith;
  rewrite <- (tmp X); clear tmp; rewrite Zpower_exp;
  try rewrite Z.pow_1_r; auto with zarith
 end.
 rewrite Pos2Z.inj_sub_max; auto with zarith.
 rewrite Z.max_r; auto with zarith.
 ring.
 repeat rewrite C0_id.
 rewrite spec_w_add_c; auto with zarith.
 intros H1; split; auto with zarith.
 rewrite add_mult_div_2_plus_1.
 rewrite Hw1.
 pattern [|w2|] at 1; rewrite (Z_div_mod_eq [|w2|] 2);
  auto with zarith.
 rewrite H1.
 unfold base.
 match goal with |- context[_ ^ ?X] =>
 assert (tmp: forall p, 1 + (p - 1) = p); auto with zarith;
  rewrite <- (tmp X); clear tmp; rewrite Zpower_exp;
  try rewrite Z.pow_1_r; auto with zarith
 end.
 rewrite Pos2Z.inj_sub_max; auto with zarith.
 rewrite Z.max_r; auto with zarith.
 ring.
 repeat rewrite C1_plus_wB in H0.
 rewrite C1_plus_wB.
 match goal with |- context[w_div21c ?y ?z ?t] =>
   generalize (@spec_w_div21c y z t H);
   case (w_div21c y z t); autorewrite with w_rewrite;
   auto
 end.
 intros c w1; case c.
 intros w2 (Hw1, Hw2); rewrite C0_id in Hw1.
 rewrite <- Zplus_mod_one in Hw1; auto with zarith.
 rewrite Zmod_small in Hw1; auto with zarith.
 match goal with |- context[w_is_even ?y] =>
   generalize (spec_w_is_even y);
   case (w_is_even y)
 end.
 repeat rewrite C0_id.
 intros H1; split; auto with zarith.
 rewrite add_mult_div_2_plus_1.
 replace (wB + [|w0|]) with ([|b|] + ([|w0|] - [|b|] + wB));
  auto with zarith.
 rewrite Z.mul_add_distr_r; rewrite <- Z.add_assoc.
 rewrite Hw1.
 pattern [|w2|] at 1; rewrite (Z_div_mod_eq [|w2|] 2);
  auto with zarith.
 rewrite H1; unfold base.
 match goal with |- context[_ ^ ?X] =>
 assert (tmp: forall p, 1 + (p - 1) = p); auto with zarith;
  rewrite <- (tmp X); clear tmp; rewrite Zpower_exp;
  try rewrite Z.pow_1_r; auto with zarith
 end.
 rewrite Pos2Z.inj_sub_max; auto with zarith.
 rewrite Z.max_r; auto with zarith.
 ring.
 repeat rewrite C0_id.
 rewrite add_mult_div_2_plus_1.
 rewrite spec_w_add_c; auto with zarith.
 intros H1; split; auto with zarith.
 replace (wB + [|w0|]) with ([|b|] + ([|w0|] - [|b|] + wB));
  auto with zarith.
 rewrite Z.mul_add_distr_r; rewrite <- Z.add_assoc.
 rewrite Hw1.
 pattern [|w2|] at 1; rewrite (Z_div_mod_eq [|w2|] 2);
  auto with zarith.
 rewrite H1; unfold base.
 match goal with |- context[_ ^ ?X] =>
 assert (tmp: forall p, 1 + (p - 1) = p); auto with zarith;
  rewrite <- (tmp X); clear tmp; rewrite Zpower_exp;
  try rewrite Z.pow_1_r; auto with zarith
 end.
 rewrite Pos2Z.inj_sub_max; auto with zarith.
 rewrite Z.max_r; auto with zarith.
 ring.
 split; auto with zarith.
 destruct (spec_to_Z b);auto with zarith.
 destruct (spec_to_Z w0);auto with zarith.
 destruct (spec_to_Z b);auto with zarith.
 destruct (spec_to_Z b);auto with zarith.
 intros w2; rewrite C1_plus_wB.
 rewrite <- Zplus_mod_one; auto with zarith.
 rewrite Zmod_small; auto with zarith.
 intros (Hw1, Hw2).
 match goal with |- context[w_is_even ?y] =>
   generalize (spec_w_is_even y);
   case (w_is_even y)
 end.
 repeat (rewrite C0_id || rewrite C1_plus_wB).
 intros H1; split; auto with zarith.
 rewrite add_mult_div_2.
 replace (wB + [|w0|]) with ([|b|] + ([|w0|] - [|b|] + wB));
  auto with zarith.
 rewrite Z.mul_add_distr_r; rewrite <- Z.add_assoc.
 rewrite Hw1.
 pattern [|w2|] at 1; rewrite (Z_div_mod_eq [|w2|] 2);
  auto with zarith.
 rewrite H1; ring.
 repeat (rewrite C0_id || rewrite C1_plus_wB).
 rewrite spec_w_add_c; auto with zarith.
 intros H1; split; auto with zarith.
 rewrite add_mult_div_2.
 replace (wB + [|w0|]) with ([|b|] + ([|w0|] - [|b|] + wB));
  auto with zarith.
 rewrite Z.mul_add_distr_r; rewrite <- Z.add_assoc.
 rewrite Hw1.
 pattern [|w2|] at 1; rewrite (Z_div_mod_eq [|w2|] 2);
  auto with zarith.
 rewrite H1; ring.
 split; auto with zarith.
 destruct (spec_to_Z b);auto with zarith.
 destruct (spec_to_Z w0);auto with zarith.
 destruct (spec_to_Z b);auto with zarith.
 destruct (spec_to_Z b);auto with zarith.
 Qed.

 Theorem wB_div_4:  4 * (wB / 4) = wB.
 Proof.
  unfold base.
  assert (2 ^ Zpos w_digits =
              4 * (2 ^ (Zpos w_digits - 2))).
  change 4 with (2 ^ 2).
  rewrite <- Zpower_exp; auto with zarith.
  f_equal; auto with zarith.
  rewrite H.
  rewrite (fun x => (Z.mul_comm 4 (2 ^x))).
  rewrite Z_div_mult; auto with zarith.
 Qed.

 Theorem Zsquare_mult: forall p, p ^ 2 = p * p.
 intros p; change 2 with (1 + 1); rewrite Zpower_exp;
  try rewrite Z.pow_1_r; auto with zarith.
 Qed.

 Theorem Zsquare_pos: forall p, 0 <= p ^ 2.
 intros p; case (Z.le_gt_cases 0 p); intros H1.
 rewrite Zsquare_mult; apply Z.mul_nonneg_nonneg; auto with zarith.
 rewrite Zsquare_mult; replace (p * p) with ((- p) * (- p)); try ring.
 apply Z.mul_nonneg_nonneg; auto with zarith.
 Qed.

 Lemma spec_split: forall x,
  [|fst (split x)|] * wB + [|snd (split x)|] = [[x]].
 intros x; case x; simpl; autorewrite with w_rewrite;
  auto with zarith.
 Qed.

 Theorem mult_wwB: forall x y, [|x|] * [|y|] < wwB.
 Proof.
  intros x y; rewrite wwB_wBwB; rewrite Z.pow_2_r.
  generalize (spec_to_Z x); intros U.
  generalize (spec_to_Z y); intros U1.
  apply Z.le_lt_trans with ((wB -1 ) * (wB - 1)); auto with zarith.
  apply Z.mul_le_mono_nonneg; auto with zarith.
  rewrite ?Z.mul_sub_distr_l, ?Z.mul_sub_distr_r; auto with zarith.
 Qed.
 Hint Resolve mult_wwB.

 Lemma spec_ww_sqrt2 : forall x y,
       wwB/ 4 <= [[x]] ->
       let (s,r) := ww_sqrt2 x y in
          [||WW x y||] = [[s]] ^ 2 + [+[r]] /\
          [+[r]] <= 2 * [[s]].
 intros x y H; unfold ww_sqrt2.
 repeat match goal with |- context[split ?x] =>
   generalize (spec_split x); case (split x)
 end; simpl @fst; simpl @snd.
 intros w0 w1 Hw0 w2 w3 Hw1.
 assert (U: wB/4 <= [|w2|]).
 case (Z.le_gt_cases (wB / 4) [|w2|]); auto; intros H1.
 contradict H; apply Z.lt_nge.
 rewrite wwB_wBwB; rewrite Z.pow_2_r.
 pattern wB at 1; rewrite <- wB_div_4; rewrite <- Z.mul_assoc;
   rewrite Z.mul_comm.
 rewrite Z_div_mult; auto with zarith.
 rewrite <- Hw1.
 match goal with |- _  < ?X =>
  pattern X; rewrite <- Z.add_0_r; apply beta_lex_inv;
  auto with zarith
 end.
 destruct (spec_to_Z w3);auto with zarith.
 generalize (@spec_w_sqrt2 w2 w3 U); case (w_sqrt2 w2 w3).
 intros w4 c (H1, H2).
 assert (U1: wB/2 <= [|w4|]).
 case (Z.le_gt_cases (wB/2) [|w4|]); auto with zarith.
 intros U1.
 assert (U2 : [|w4|] <= wB/2 -1); auto with zarith.
 assert (U3 : [|w4|] ^ 2 <= wB/4 * wB - wB + 1); auto with zarith.
 match goal with |- ?X ^ 2 <= ?Y =>
  rewrite Zsquare_mult;
  replace Y with ((wB/2 - 1) * (wB/2 -1))
 end.
 apply Z.mul_le_mono_nonneg; auto with zarith.
 destruct (spec_to_Z w4);auto with zarith.
 destruct (spec_to_Z w4);auto with zarith.
 pattern wB at 4 5; rewrite <- wB_div_2.
 rewrite Z.mul_assoc.
 replace ((wB / 4) * 2) with (wB / 2).
 ring.
 pattern wB at 1; rewrite <- wB_div_4.
 change 4 with (2 * 2).
 rewrite <- Z.mul_assoc; rewrite (Z.mul_comm 2).
 rewrite Z_div_mult; try ring; auto with zarith.
 assert (U4 : [+|c|]  <= wB -2); auto with zarith.
 apply Z.le_trans with (1 := H2).
 match goal with |- ?X <= ?Y =>
  replace Y with (2 * (wB/ 2 - 1)); auto with zarith
 end.
 pattern wB at 2; rewrite <- wB_div_2; auto with zarith.
 match type of H1 with ?X = _ =>
  assert (U5: X < wB / 4 * wB)
 end.
 rewrite H1; auto with zarith.
 contradict U; apply Z.lt_nge.
 apply Z.mul_lt_mono_pos_r with wB; auto with zarith.
 destruct (spec_to_Z w4);auto with zarith.
 apply Z.le_lt_trans with (2 := U5).
 unfold ww_to_Z, zn2z_to_Z.
 destruct (spec_to_Z w3);auto with zarith.
 generalize (@spec_w_div2s c w0 w4 U1 H2).
 case (w_div2s c w0 w4).
 intros c0; case c0; intros w5;
   repeat (rewrite C0_id || rewrite C1_plus_wB).
 intros c1; case c1; intros w6;
   repeat (rewrite C0_id || rewrite C1_plus_wB).
 intros (H3, H4).
 match goal with |- context [ww_sub_c ?y ?z] =>
  generalize (spec_ww_sub_c y z); case (ww_sub_c y z)
 end.
 intros z; change [-[C0 z]] with ([[z]]).
 change [+[C0 z]] with ([[z]]).
 intros H5; rewrite spec_w_square_c in H5;
  auto.
 split.
 unfold zn2z_to_Z; rewrite <- Hw1.
 unfold ww_to_Z, zn2z_to_Z in H1. rewrite H1.
 rewrite <- Hw0.
 match goal with |- (?X ^2 + ?Y) * wwB + (?Z * wB + ?T) = ?U =>
  transitivity ((X * wB) ^ 2 + (Y * wB + Z) * wB + T)
 end.
 repeat rewrite Zsquare_mult.
 rewrite wwB_wBwB; ring.
 rewrite H3.
 rewrite H5.
 unfold ww_to_Z, zn2z_to_Z.
 repeat rewrite Zsquare_mult; ring.
 rewrite H5.
 unfold ww_to_Z, zn2z_to_Z.
 match goal with |- ?X - ?Y * ?Y <= _ =>
  assert (V := Zsquare_pos Y);
  rewrite Zsquare_mult in V;
  apply Z.le_trans with X; auto with zarith;
  clear V
 end.
 match goal with |- ?X * wB + ?Y <= 2 * (?Z * wB + ?T) =>
  apply Z.le_trans with ((2 * Z - 1) * wB + wB); auto with zarith
 end.
 destruct (spec_to_Z w1);auto with zarith.
 match goal with |- ?X <= _ =>
  replace X with (2 * [|w4|] * wB); auto with zarith
 end.
 rewrite Z.mul_add_distr_l; rewrite Z.mul_assoc.
 destruct (spec_to_Z w5); auto with zarith.
 ring.
 intros z; replace [-[C1 z]] with (- wwB + [[z]]).
 2: simpl; case wwB; auto with zarith.
 intros H5; rewrite spec_w_square_c in H5;
  auto.
 match goal with |- context [ww_pred_c ?y] =>
  generalize (spec_ww_pred_c y); case (ww_pred_c y)
 end.
 intros z1; change [-[C0 z1]] with ([[z1]]).
 rewrite ww_add_mult_mult_2.
 rewrite spec_ww_add_c.
 rewrite spec_ww_pred.
 rewrite <- Zmod_unique with (q := 1) (r := -wwB + 2 * [[WW w4 w5]]);
  auto with zarith.
 intros Hz1; rewrite Zmod_small; auto with zarith.
 match type of H5 with -?X + ?Y = ?Z =>
  assert (V: Y = Z + X);
  try (rewrite <- H5; ring)
 end.
 split.
 unfold zn2z_to_Z; rewrite <- Hw1.
 unfold ww_to_Z, zn2z_to_Z in H1; rewrite H1.
 rewrite <- Hw0.
 match goal with |- (?X ^2 + ?Y) * wwB + (?Z * wB + ?T) = ?U =>
  transitivity ((X * wB) ^ 2 + (Y * wB + Z) * wB + T)
 end.
 repeat rewrite Zsquare_mult.
 rewrite wwB_wBwB; ring.
 rewrite H3.
 rewrite V.
 rewrite Hz1.
 unfold ww_to_Z; simpl zn2z_to_Z.
 repeat rewrite Zsquare_mult; ring.
 rewrite Hz1.
 destruct (spec_ww_to_Z w_digits w_to_Z spec_to_Z z);auto with zarith.
 assert (V1 := spec_ww_to_Z w_digits w_to_Z spec_to_Z (WW w4 w5)).
 assert (0 <  [[WW w4 w5]]); auto with zarith.
 apply Z.lt_le_trans with (wB/ 2 * wB + 0); auto with zarith.
 autorewrite with rm10; apply Z.mul_pos_pos; auto with zarith.
 apply Z.mul_lt_mono_pos_r with 2; auto with zarith.
 autorewrite with rm10.
 rewrite Z.mul_comm; rewrite wB_div_2; auto with zarith.
 case (spec_to_Z w5);auto with zarith.
 case (spec_to_Z w5);auto with zarith.
 simpl.
 assert (V2 := spec_to_Z w5);auto with zarith.
 assert (V1 := spec_ww_to_Z w_digits w_to_Z spec_to_Z (WW w4 w5)); auto with zarith.
 split; auto with zarith.
 assert (wwB <= 2 * [[WW w4 w5]]); auto with zarith.
 apply Z.le_trans with (2 * ([|w4|] * wB)).
 rewrite wwB_wBwB; rewrite Z.pow_2_r.
 rewrite Z.mul_assoc; apply Z.mul_le_mono_nonneg_r; auto with zarith.
 assert (V2 := spec_to_Z w5);auto with zarith.
 rewrite <- wB_div_2; auto with zarith.
 simpl ww_to_Z; assert (V2 := spec_to_Z w5);auto with zarith.
 assert (V1 := spec_ww_to_Z w_digits w_to_Z spec_to_Z (WW w4 w5)); auto with zarith.
 intros z1; change [-[C1 z1]] with (-wwB + [[z1]]).
 match goal with |- context[([+[C0 ?z]])] =>
   change [+[C0 z]] with ([[z]])
 end.
 rewrite spec_ww_add; auto with zarith.
 rewrite spec_ww_pred; auto with zarith.
 rewrite ww_add_mult_mult_2.
 rename V1 into VV1.
 assert (VV2: 0 <  [[WW w4 w5]]); auto with zarith.
 apply Z.lt_le_trans with (wB/ 2 * wB + 0); auto with zarith.
 autorewrite with rm10; apply Z.mul_pos_pos; auto with zarith.
 apply Z.mul_lt_mono_pos_r with 2; auto with zarith.
 autorewrite with rm10.
 rewrite Z.mul_comm; rewrite wB_div_2; auto with zarith.
 assert (VV3 := spec_to_Z w5);auto with zarith.
 assert (VV3 := spec_to_Z w5);auto with zarith.
 simpl.
 assert (VV3 := spec_to_Z w5);auto with zarith.
 assert (VV3: wwB <= 2 * [[WW w4 w5]]); auto with zarith.
 apply Z.le_trans with (2 * ([|w4|] * wB)).
 rewrite wwB_wBwB; rewrite Z.pow_2_r.
 rewrite Z.mul_assoc; apply Z.mul_le_mono_nonneg_r; auto with zarith.
 case (spec_to_Z w5);auto with zarith.
 rewrite <- wB_div_2; auto with zarith.
 simpl ww_to_Z; assert (V4 := spec_to_Z w5);auto with zarith.
 rewrite <- Zmod_unique with (q := 1) (r := -wwB + 2 * [[WW w4 w5]]);
  auto with zarith.
 intros Hz1; rewrite Zmod_small; auto with zarith.
 match type of H5 with -?X + ?Y = ?Z =>
  assert (V: Y = Z + X);
  try (rewrite <- H5; ring)
 end.
 match type of Hz1 with -?X + ?Y = -?X + ?Z - 1 =>
  assert (V1: Y = Z - 1);
  [replace (Z - 1) with (X + (-X + Z -1));
    [rewrite <- Hz1 | idtac]; ring
    | idtac]
 end.
 rewrite <- Zmod_unique with (q := 1) (r := -wwB + [[z1]] + [[z]]);
  auto with zarith.
 unfold zn2z_to_Z; rewrite <- Hw1.
 unfold ww_to_Z, zn2z_to_Z in H1; rewrite H1.
 rewrite <- Hw0.
 split.
 match goal with |- (?X ^2 + ?Y) * wwB + (?Z * wB + ?T) = ?U =>
  transitivity ((X * wB) ^ 2 + (Y * wB + Z) * wB + T)
 end.
 repeat rewrite Zsquare_mult.
 rewrite wwB_wBwB; ring.
 rewrite H3.
 rewrite V.
 rewrite Hz1.
 unfold ww_to_Z; simpl zn2z_to_Z.
 repeat rewrite Zsquare_mult; ring.
 assert (V2 := spec_ww_to_Z w_digits w_to_Z spec_to_Z z);auto with zarith.
 assert (V2 := spec_ww_to_Z w_digits w_to_Z spec_to_Z z);auto with zarith.
 assert (V3 := spec_ww_to_Z w_digits w_to_Z spec_to_Z z1);auto with zarith.
 split; auto with zarith.
 rewrite (Z.add_comm (-wwB)); rewrite <- Z.add_assoc.
 rewrite H5.
 match goal with |- 0 <= ?X + (?Y - ?Z)  =>
  apply Z.le_trans with (X - Z); auto with zarith
 end.
 2: generalize (spec_ww_to_Z w_digits w_to_Z spec_to_Z (WW w6 w1)); unfold ww_to_Z; auto with zarith.
 rewrite V1.
 match goal with |- 0 <= ?X - 1 - ?Y =>
   assert (Y < X); auto with zarith
 end.
 apply Z.lt_le_trans with wwB; auto with zarith.
 intros (H3, H4).
 match goal with |- context [ww_sub_c ?y ?z] =>
  generalize (spec_ww_sub_c y z); case (ww_sub_c y z)
 end.
 intros z; change [-[C0 z]] with ([[z]]).
 match goal with |- context[([+[C1 ?z]])] =>
   replace [+[C1 z]] with (wwB + [[z]])
 end.
 2: simpl; case wwB; auto.
 intros H5; rewrite spec_w_square_c in H5;
  auto.
 split.
 change ([||WW x y||]) with ([[x]] * wwB + [[y]]).
 rewrite <- Hw1.
 unfold ww_to_Z, zn2z_to_Z in H1; rewrite H1.
 rewrite <- Hw0.
 match goal with |- (?X ^2 + ?Y) * wwB + (?Z * wB + ?T) = ?U =>
  transitivity ((X * wB) ^ 2 + (Y * wB + Z) * wB + T)
 end.
 repeat rewrite Zsquare_mult.
 rewrite wwB_wBwB; ring.
 rewrite H3.
 rewrite H5.
 unfold ww_to_Z; simpl zn2z_to_Z.
 rewrite wwB_wBwB.
 repeat rewrite Zsquare_mult; ring.
 simpl ww_to_Z.
 rewrite H5.
 simpl ww_to_Z.
 rewrite wwB_wBwB; rewrite Z.pow_2_r.
 match goal with |- ?X * ?Y + (?Z * ?Y + ?T - ?U) <= _ =>
  apply Z.le_trans with (X * Y + (Z * Y + T - 0));
  auto with zarith
 end.
 assert (V := Zsquare_pos [|w5|]);
 rewrite Zsquare_mult in V; auto with zarith.
 autorewrite with rm10.
 match goal with |- _ <= 2 * (?U * ?V + ?W) =>
  apply Z.le_trans with (2 * U * V + 0);
  auto with zarith
 end.
 match goal with |- ?X * ?Y + (?Z * ?Y + ?T) <= _ =>
  replace (X * Y + (Z * Y + T)) with ((X + Z) * Y + T);
  try ring
 end.
 apply Z.lt_le_incl; apply beta_lex_inv; auto with zarith.
 destruct (spec_to_Z w1);auto with zarith.
 destruct (spec_to_Z w5);auto with zarith.
 rewrite Z.mul_add_distr_l; auto with zarith.
 rewrite Z.mul_assoc; auto with zarith.
 intros z; replace [-[C1 z]] with (- wwB + [[z]]).
 2: simpl; case wwB; auto with zarith.
 intros H5; rewrite spec_w_square_c in H5;
  auto.
 match goal with |- context[([+[C0 ?z]])] =>
   change [+[C0 z]] with ([[z]])
 end.
 match type of H5 with -?X + ?Y = ?Z =>
  assert (V: Y = Z + X);
  try (rewrite <- H5; ring)
 end.
 change ([||WW x y||]) with ([[x]] * wwB + [[y]]).
 simpl ww_to_Z.
 rewrite <- Hw1.
 simpl ww_to_Z in H1; rewrite H1.
 rewrite <- Hw0.
 split.
 match goal with |- (?X ^2 + ?Y) * wwB + (?Z * wB + ?T) = ?U =>
  transitivity ((X * wB) ^ 2 + (Y * wB + Z) * wB + T)
 end.
 repeat rewrite Zsquare_mult.
 rewrite wwB_wBwB; ring.
 rewrite H3.
 rewrite V.
 simpl ww_to_Z.
 rewrite wwB_wBwB.
 repeat rewrite Zsquare_mult; ring.
 rewrite V.
 simpl ww_to_Z.
 rewrite wwB_wBwB; rewrite Z.pow_2_r.
 match goal with |- (?Z * ?Y + ?T - ?U) + ?X * ?Y <= _ =>
  apply Z.le_trans with ((Z * Y + T - 0) + X * Y);
  auto with zarith
 end.
 assert (V1 := Zsquare_pos [|w5|]);
 rewrite Zsquare_mult in V1; auto with zarith.
 autorewrite with rm10.
 match goal with |- _ <= 2 * (?U * ?V + ?W) =>
  apply Z.le_trans with (2 * U * V + 0);
  auto with zarith
 end.
 match goal with |- (?Z * ?Y + ?T) + ?X * ?Y  <= _ =>
  replace ((Z * Y + T) + X * Y) with ((X + Z) * Y + T);
  try ring
 end.
 apply Z.lt_le_incl; apply beta_lex_inv; auto with zarith.
 destruct (spec_to_Z w1);auto with zarith.
 destruct (spec_to_Z w5);auto with zarith.
 rewrite Z.mul_add_distr_l; auto with zarith.
 rewrite Z.mul_assoc; auto with zarith.
 Z.le_elim H2.
 intros c1 (H3, H4).
 match type of H3 with ?X = ?Y => absurd (X < Y) end.
 apply Z.le_ngt; rewrite <- H3; auto with zarith.
 rewrite Z.mul_add_distr_r.
 apply Z.lt_le_trans with ((2 * [|w4|]) * wB + 0);
  auto with zarith.
 apply beta_lex_inv; auto with zarith.
 destruct (spec_to_Z w0);auto with zarith.
 assert (V1 := spec_to_Z w5);auto with zarith.
 rewrite (Z.mul_comm wB); auto with zarith.
 assert (0 <= [|w5|] * (2 * [|w4|])); auto with zarith.
 intros c1 (H3, H4); rewrite H2 in H3.
 match type of H3 with ?X + ?Y = (?Z + ?T) * ?U + ?V =>
  assert (VV: (Y = (T * U) + V));
  [replace Y with ((X + Y) - X);
    [rewrite H3; ring | ring] | idtac]
 end.
 assert (V1 := spec_to_Z w0);auto with zarith.
 assert (V2 := spec_to_Z w5);auto with zarith.
 case V2; intros V3 _.
 Z.le_elim V3; auto with zarith.
 match type of VV with ?X = ?Y => absurd (X < Y) end.
 apply Z.le_ngt; rewrite <- VV; auto with zarith.
 apply Z.lt_le_trans with wB; auto with zarith.
 match goal with |- _ <= ?X + _ =>
  apply Z.le_trans with X; auto with zarith
 end.
 match goal with |- _ <= _ * ?X =>
  apply Z.le_trans with (1 * X); auto with zarith
 end.
 autorewrite with rm10.
 rewrite <- wB_div_2; apply Z.mul_le_mono_nonneg_l; auto with zarith.
 rewrite <- V3 in VV; generalize VV; autorewrite with rm10;
 clear VV; intros VV.
 rewrite spec_ww_add_c; auto with zarith.
 rewrite ww_add_mult_mult_2_plus_1.
 match goal with |- context[?X mod wwB] =>
   rewrite <- Zmod_unique with (q := 1) (r := -wwB + X)
 end; auto with zarith.
 simpl ww_to_Z.
 rewrite spec_w_Bm1; auto with zarith.
 split.
 change ([||WW x y||]) with ([[x]] * wwB + [[y]]).
 rewrite <- Hw1.
 simpl ww_to_Z in H1; rewrite H1.
 rewrite <- Hw0.
 match goal with |- (?X ^2 + ?Y) * wwB + (?Z * wB + ?T) = ?U =>
  transitivity ((X * wB) ^ 2 + (Y * wB + Z) * wB + T)
 end.
 repeat rewrite Zsquare_mult.
 rewrite wwB_wBwB; ring.
 rewrite H2.
 rewrite wwB_wBwB.
 repeat rewrite Zsquare_mult; ring.
 assert (V4 := spec_ww_to_Z w_digits w_to_Z spec_to_Z y);auto with zarith.
 assert (V4 := spec_ww_to_Z w_digits w_to_Z spec_to_Z y);auto with zarith.
 simpl ww_to_Z; unfold ww_to_Z.
 rewrite spec_w_Bm1; auto with zarith.
 split.
 rewrite wwB_wBwB; rewrite Z.pow_2_r.
 match goal with |- _ <= -?X + (2 * (?Z * ?T + ?U) + ?V) =>
  assert (X <= 2 * Z * T); auto with zarith
 end.
 apply Z.mul_le_mono_nonneg_r; auto with zarith.
 rewrite <- wB_div_2; apply Z.mul_le_mono_nonneg_l; auto with zarith.
 rewrite Z.mul_add_distr_l; auto with zarith.
 rewrite Z.mul_assoc; auto with zarith.
 match goal with |- _ + ?X  < _ =>
  replace X with ((2 * (([|w4|]) + 1) * wB) - 1); try ring
 end.
 assert (2 * ([|w4|] + 1) * wB <= 2 * wwB); auto with zarith.
 rewrite <- Z.mul_assoc; apply Z.mul_le_mono_nonneg_l; auto with zarith.
 rewrite wwB_wBwB; rewrite Z.pow_2_r.
 apply Z.mul_le_mono_nonneg_r; auto with zarith.
 case (spec_to_Z w4);auto with zarith.
Qed.

 Lemma spec_ww_is_zero: forall x,
   if ww_is_zero x then [[x]] = 0 else 0 < [[x]].
  intro x; unfold ww_is_zero.
  rewrite spec_ww_compare. case Z.compare_spec;
   auto with zarith.
  simpl ww_to_Z.
  assert (V4 := spec_ww_to_Z w_digits w_to_Z spec_to_Z x);auto with zarith.
  Qed.

  Lemma wwB_4_2: 2 * (wwB / 4) = wwB/ 2.
  pattern wwB at 1; rewrite wwB_wBwB; rewrite Z.pow_2_r.
  rewrite <- wB_div_2.
  match goal with |- context[(2 * ?X) * (2 * ?Z)] =>
    replace ((2 * X) * (2 * Z)) with ((X * Z) * 4); try ring
  end.
  rewrite Z_div_mult; auto with zarith.
  rewrite Z.mul_assoc; rewrite wB_div_2.
  rewrite wwB_div_2; ring.
  Qed.


  Lemma spec_ww_head1
       : forall x : zn2z w,
         (ww_is_even (ww_head1 x) = true) /\
         (0 < [[x]] -> wwB / 4 <= 2 ^ [[ww_head1 x]] * [[x]] < wwB).
  assert (U := wB_pos w_digits).
  intros x; unfold ww_head1.
  generalize (spec_ww_is_even (ww_head0 x)); case_eq (ww_is_even (ww_head0 x)).
    intros HH H1; rewrite HH; split; auto.
  intros H2.
  generalize (spec_ww_head0 x H2); case (ww_head0 x);  autorewrite with rm10.
  intros (H3, H4); split; auto with zarith.
  apply Z.le_trans with (2 := H3).
  apply Zdiv_le_compat_l; auto with zarith.
  intros xh xl (H3, H4); split; auto with zarith.
  apply Z.le_trans with (2 := H3).
  apply Zdiv_le_compat_l; auto with zarith.
  intros H1.
  case (spec_to_w_Z (ww_head0 x)); intros Hv1 Hv2.
  assert (Hp0: 0 < [[ww_head0 x]]).
    generalize (spec_ww_is_even (ww_head0 x)); rewrite H1.
    generalize Hv1; case [[ww_head0 x]].
    rewrite Zmod_small; auto with zarith.
    intros; assert (0 < Zpos p); auto with zarith.
    red; simpl; auto.
    intros p H2; case H2; auto.
  assert (Hp: [[ww_pred (ww_head0 x)]] = [[ww_head0 x]] - 1).
    rewrite spec_ww_pred.
    rewrite Zmod_small; auto with zarith.
  intros H2; split.
    generalize (spec_ww_is_even (ww_pred (ww_head0 x)));
      case ww_is_even; auto.
    rewrite Hp.
    rewrite Zminus_mod; auto with zarith.
    rewrite H2; repeat rewrite Zmod_small; auto with zarith.
  intros H3; rewrite Hp.
  case (spec_ww_head0 x); auto; intros Hv3 Hv4.
  assert (Hu: forall u, 0 < u -> 2 *  2 ^ (u - 1) = 2 ^u).
    intros u Hu.
    pattern 2 at 1; rewrite <- Z.pow_1_r.
    rewrite <- Zpower_exp; auto with zarith.
    ring_simplify (1 + (u - 1)); auto with zarith.
  split; auto with zarith.
  apply Z.mul_le_mono_pos_r with 2; auto with zarith.
  repeat rewrite (fun x => Z.mul_comm x 2).
  rewrite wwB_4_2.
  rewrite Z.mul_assoc; rewrite Hu; auto with zarith.
  apply Z.le_lt_trans with (2 * 2 ^ ([[ww_head0 x]] - 1) * [[x]]); auto with zarith;
    rewrite Hu; auto with zarith.
  apply Z.mul_le_mono_nonneg_r; auto with zarith.
  apply Zpower_le_monotone; auto with zarith.
  Qed.

  Theorem wwB_4_wB_4: wwB / 4 = wB / 4 * wB.
  Proof.
  symmetry; apply Zdiv_unique with 0; auto with zarith.
  rewrite Z.mul_assoc; rewrite wB_div_4; auto with zarith.
  rewrite wwB_wBwB; ring.
  Qed.

  Lemma spec_ww_sqrt : forall x,
       [[ww_sqrt x]] ^ 2 <= [[x]] < ([[ww_sqrt x]] + 1) ^ 2.
  assert (U := wB_pos w_digits).
  intro x; unfold ww_sqrt.
  generalize (spec_ww_is_zero x); case (ww_is_zero x).
  simpl ww_to_Z; simpl Z.pow; unfold Z.pow_pos; simpl;
    auto with zarith.
  intros H1.
  rewrite spec_ww_compare. case Z.compare_spec;
    simpl ww_to_Z; autorewrite with rm10.
  generalize H1; case x.
  intros HH; contradict HH; simpl ww_to_Z; auto with zarith.
  intros w0 w1; simpl ww_to_Z; autorewrite with w_rewrite rm10.
  intros H2; case (spec_ww_head1 (WW w0 w1)); intros H3 H4 H5.
  generalize (H4 H2); clear H4; rewrite H5; clear H5; autorewrite with rm10.
  intros (H4, H5).
  assert (V: wB/4 <= [|w0|]).
  apply beta_lex with 0 [|w1|] wB; auto with zarith; autorewrite with rm10.
  rewrite <- wwB_4_wB_4; auto.
  generalize (@spec_w_sqrt2 w0 w1 V);auto with zarith.
  case (w_sqrt2 w0 w1); intros w2 c.
  simpl ww_to_Z; simpl @fst.
  case c; unfold interp_carry; autorewrite with rm10.
  intros w3 (H6, H7); rewrite H6.
  assert (V1 := spec_to_Z w3);auto with zarith.
  split; auto with zarith.
  apply Z.le_lt_trans with ([|w2|] ^2  + 2 * [|w2|]); auto with zarith.
  match goal with |- ?X < ?Z =>
    replace Z with (X + 1); auto with zarith
  end.
  repeat rewrite Zsquare_mult; ring.
  intros w3 (H6, H7); rewrite H6.
  assert (V1 := spec_to_Z w3);auto with zarith.
  split; auto with zarith.
  apply Z.le_lt_trans with ([|w2|] ^2  + 2 * [|w2|]); auto with zarith.
  match goal with |- ?X < ?Z =>
    replace Z with (X + 1); auto with zarith
  end.
  repeat rewrite Zsquare_mult; ring.
  intros HH; case (spec_to_w_Z (ww_head1 x)); auto with zarith.
  intros Hv1.
  case (spec_ww_head1 x); intros Hp1 Hp2.
  generalize (Hp2 H1); clear Hp2; intros Hp2.
  assert (Hv2: [[ww_head1 x]] <= Zpos (xO w_digits)).
    case (Z.le_gt_cases (Zpos (xO w_digits)) [[ww_head1 x]]); auto with zarith; intros HH1.
    case Hp2; intros _ HH2; contradict HH2.
    apply Z.le_ngt; unfold base.
    apply Z.le_trans with (2 ^ [[ww_head1 x]]).
      apply Zpower_le_monotone; auto with zarith.
    pattern (2 ^ [[ww_head1 x]]) at 1;
      rewrite <- (Z.mul_1_r (2 ^ [[ww_head1 x]])).
    apply Z.mul_le_mono_nonneg_l; auto with zarith.
  generalize (spec_ww_add_mul_div x W0 (ww_head1 x) Hv2);
     case ww_add_mul_div.
  simpl ww_to_Z; autorewrite with w_rewrite rm10.
  rewrite Zmod_small; auto with zarith.
  intros H2. symmetry in H2. rewrite Z.mul_eq_0 in H2. destruct H2 as [H2|H2].
  rewrite H2; unfold Z.pow, Z.pow_pos; simpl; auto with zarith.
  match type of H2 with ?X = ?Y =>
   absurd (Y < X); try (rewrite H2; auto with zarith; fail)
  end.
  apply Z.pow_pos_nonneg; auto with zarith.
  split; auto with zarith.
  case Hp2; intros _ tmp; apply Z.le_lt_trans with (2 := tmp);
   clear tmp.
  rewrite Z.mul_comm; apply Z.mul_le_mono_nonneg_r; auto with zarith.
  assert (Hv0: [[ww_head1 x]] = 2 * ([[ww_head1 x]]/2)).
    pattern [[ww_head1 x]] at 1; rewrite (Z_div_mod_eq [[ww_head1 x]] 2);
      auto with zarith.
    generalize (spec_ww_is_even (ww_head1 x)); rewrite Hp1;
      intros tmp; rewrite tmp; rewrite Z.add_0_r; auto.
  intros w0 w1; autorewrite with w_rewrite rm10.
  rewrite Zmod_small; auto with zarith.
  2: rewrite Z.mul_comm; auto with zarith.
  intros H2.
  assert (V: wB/4 <= [|w0|]).
  apply beta_lex with 0 [|w1|] wB; auto with zarith; autorewrite with rm10.
  simpl ww_to_Z in H2; rewrite H2.
  rewrite <- wwB_4_wB_4; auto with zarith.
  rewrite Z.mul_comm; auto with zarith.
  assert (V1 := spec_to_Z w1);auto with zarith.
  generalize (@spec_w_sqrt2 w0 w1 V);auto with zarith.
  case (w_sqrt2 w0 w1); intros w2 c.
  case (spec_to_Z w2); intros HH1 HH2.
  simpl ww_to_Z; simpl @fst.
  assert (Hv3: [[ww_pred ww_zdigits]]
                 = Zpos (xO w_digits) - 1).
    rewrite spec_ww_pred; rewrite spec_ww_zdigits.
    rewrite Zmod_small; auto with zarith.
    split; auto with zarith.
    apply Z.lt_le_trans with (Zpos (xO w_digits)); auto with zarith.
    unfold base; apply Zpower2_le_lin; auto with zarith.
  assert (Hv4: [[ww_head1 x]]/2 < wB).
    apply Z.le_lt_trans with (Zpos w_digits).
    apply Z.mul_le_mono_pos_r with 2; auto with zarith.
    repeat rewrite (fun x => Z.mul_comm x 2).
    rewrite <- Hv0;  rewrite <- Pos2Z.inj_xO; auto.
    unfold base; apply Zpower2_lt_lin; auto with zarith.
  assert (Hv5: [[(ww_add_mul_div (ww_pred ww_zdigits) W0 (ww_head1 x))]]
                 = [[ww_head1 x]]/2).
    rewrite spec_ww_add_mul_div.
    simpl ww_to_Z; autorewrite with rm10.
    rewrite Hv3.
    ring_simplify (Zpos (xO w_digits) - (Zpos (xO w_digits) - 1)).
    rewrite Z.pow_1_r.
    rewrite Zmod_small; auto with zarith.
    split; auto with zarith.
    apply Z.lt_le_trans with (1 := Hv4); auto with zarith.
    unfold base; apply Zpower_le_monotone; auto with zarith.
    split; unfold ww_digits; try rewrite Pos2Z.inj_xO; auto with zarith.
    rewrite Hv3; auto with zarith.
  assert (Hv6: [|low(ww_add_mul_div (ww_pred ww_zdigits) W0 (ww_head1 x))|]
                 = [[ww_head1 x]]/2).
    rewrite spec_low.
    rewrite Hv5; rewrite Zmod_small; auto with zarith.
  rewrite spec_w_add_mul_div; auto with zarith.
  rewrite spec_w_sub; auto with zarith.
  rewrite spec_w_0.
  simpl ww_to_Z; autorewrite with rm10.
  rewrite Hv6; rewrite spec_w_zdigits.
  rewrite (fun x y => Zmod_small (x - y)).
  ring_simplify (Zpos w_digits - (Zpos w_digits - [[ww_head1 x]] / 2)).
  rewrite Zmod_small.
  simpl ww_to_Z in H2; rewrite H2; auto with zarith.
  intros (H4, H5); split.
  apply Z.mul_le_mono_pos_r with (2 ^ [[ww_head1 x]]); auto with zarith.
  rewrite H4.
  apply Z.le_trans with ([|w2|] ^ 2); auto with zarith.
  rewrite Z.mul_comm.
  pattern [[ww_head1 x]] at 1;
    rewrite Hv0; auto with zarith.
  rewrite (Z.mul_comm 2); rewrite Z.pow_mul_r;
    auto with zarith.
  assert (tmp: forall p q, p ^ 2 * q ^ 2 = (p * q) ^2);
   try (intros; repeat rewrite Zsquare_mult; ring);
   rewrite tmp; clear tmp.
  apply Zpower_le_monotone3; auto with zarith.
  split; auto with zarith.
  pattern [|w2|] at 2;
     rewrite (Z_div_mod_eq [|w2|] (2 ^ ([[ww_head1 x]] / 2)));
     auto with zarith.
  match goal with |- ?X <= ?X + ?Y =>
    assert (0 <= Y); auto with zarith
  end.
  case (Z_mod_lt [|w2|] (2 ^ ([[ww_head1 x]] / 2))); auto with zarith.
  case c; unfold interp_carry; autorewrite with rm10;
    intros w3; assert (V3 := spec_to_Z w3);auto with zarith.
  apply Z.mul_lt_mono_pos_r with (2 ^ [[ww_head1 x]]); auto with zarith.
  rewrite H4.
  apply Z.le_lt_trans with ([|w2|] ^ 2 + 2 * [|w2|]); auto with zarith.
  apply Z.lt_le_trans with (([|w2|] + 1) ^ 2); auto with zarith.
  match goal with |- ?X < ?Y =>
    replace Y with (X + 1); auto with zarith
  end.
  repeat rewrite (Zsquare_mult); ring.
  rewrite Z.mul_comm.
  pattern [[ww_head1 x]] at 1; rewrite Hv0.
  rewrite (Z.mul_comm 2); rewrite Z.pow_mul_r;
   auto with zarith.
  assert (tmp: forall p q, p ^ 2 * q ^ 2 = (p * q) ^2);
   try (intros; repeat rewrite Zsquare_mult; ring);
   rewrite tmp; clear tmp.
  apply Zpower_le_monotone3; auto with zarith.
  split; auto with zarith.
  pattern [|w2|] at 1; rewrite (Z_div_mod_eq [|w2|] (2 ^ ([[ww_head1 x]]/2)));
    auto with zarith.
  rewrite <- Z.add_assoc; rewrite Z.mul_add_distr_l.
  autorewrite with rm10; apply Z.add_le_mono_l; auto with zarith.
  case (Z_mod_lt [|w2|] (2 ^ ([[ww_head1 x]]/2))); auto with zarith.
  split; auto with zarith.
  apply Z.le_lt_trans with ([|w2|]); auto with zarith.
  apply Zdiv_le_upper_bound; auto with zarith.
  pattern [|w2|] at 1; replace [|w2|] with ([|w2|] * 2 ^0);
    auto with zarith.
  apply Z.mul_le_mono_nonneg_l; auto with zarith.
  apply Zpower_le_monotone; auto with zarith.
  rewrite Z.pow_0_r; autorewrite with rm10; auto.
  split; auto with zarith.
  rewrite Hv0 in Hv2; rewrite (Pos2Z.inj_xO w_digits) in Hv2; auto with zarith.
  apply Z.le_lt_trans with (Zpos w_digits); auto with zarith.
  unfold base; apply Zpower2_lt_lin; auto with zarith.
  rewrite spec_w_sub; auto with zarith.
  rewrite Hv6; rewrite spec_w_zdigits; auto with zarith.
  assert (Hv7: 0 < [[ww_head1 x]]/2); auto with zarith.
  rewrite Zmod_small; auto with zarith.
  split; auto with zarith.
  assert ([[ww_head1 x]]/2 <= Zpos w_digits); auto with zarith.
  apply Z.mul_le_mono_pos_r with 2; auto with zarith.
  repeat rewrite (fun x => Z.mul_comm x 2).
  rewrite <- Hv0; rewrite <- Pos2Z.inj_xO; auto with zarith.
  apply Z.le_lt_trans with (Zpos w_digits); auto with zarith.
  unfold base; apply Zpower2_lt_lin; auto with zarith.
  Qed.

End DoubleSqrt.

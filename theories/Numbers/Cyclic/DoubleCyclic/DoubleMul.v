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

Section DoubleMul.
 Variable w : Type.
 Variable w_0 : w.
 Variable w_1 : w.
 Variable w_WW : w -> w -> zn2z w.
 Variable w_W0 : w -> zn2z w.
 Variable w_0W : w -> zn2z w.
 Variable w_compare : w -> w -> comparison.
 Variable w_succ : w -> w.
 Variable w_add_c : w -> w -> carry w.
 Variable w_add : w -> w -> w.
 Variable w_sub: w -> w -> w.
 Variable w_mul_c : w -> w -> zn2z w.
 Variable w_mul : w -> w -> w.
 Variable w_square_c : w -> zn2z w.
 Variable ww_add_c : zn2z w -> zn2z w -> carry (zn2z w).
 Variable ww_add   : zn2z w -> zn2z w -> zn2z w.
 Variable ww_add_carry : zn2z w -> zn2z w -> zn2z w.
 Variable ww_sub_c : zn2z w -> zn2z w -> carry (zn2z w).
 Variable ww_sub   : zn2z w -> zn2z w -> zn2z w.

 (* ** Multiplication ** *)

 (*   (xh*B+xl) (yh*B + yl)
   xh*yh         = hh  = |hhh|hhl|B2
   xh*yl +xl*yh  = cc  =     |cch|ccl|B
   xl*yl         = ll  =         |llh|lll
  *)

 Definition double_mul_c (cross:w->w->w->w->zn2z w -> zn2z w -> w*zn2z w) x y :=
  match x, y with
  | W0, _ => W0
  | _, W0 => W0
  | WW xh xl, WW yh yl =>
    let hh := w_mul_c xh yh in
    let ll := w_mul_c xl yl in
    let (wc,cc) := cross xh xl yh yl hh ll in
    match cc with
    | W0 => WW (ww_add hh (w_W0 wc)) ll
    | WW cch ccl =>
      match ww_add_c (w_W0 ccl) ll with
      | C0 l => WW (ww_add hh (w_WW wc cch)) l
      | C1 l => WW (ww_add_carry hh (w_WW wc cch)) l
      end
    end
  end.

 Definition ww_mul_c :=
  double_mul_c
    (fun xh xl yh yl hh ll=>
      match ww_add_c (w_mul_c xh yl) (w_mul_c xl yh) with
      | C0 cc => (w_0, cc)
      | C1 cc => (w_1, cc)
      end).

 Definition w_2 := w_add w_1 w_1.

 Definition kara_prod xh xl yh yl hh ll :=
    match ww_add_c hh ll with
      C0 m =>
         match w_compare xl xh with
           Eq => (w_0, m)
         | Lt =>
           match w_compare yl yh with
             Eq => (w_0, m)
           | Lt => (w_0, ww_sub m (w_mul_c (w_sub xh xl) (w_sub yh yl)))
           | Gt => match ww_add_c m (w_mul_c (w_sub xh xl) (w_sub yl yh)) with
                      C1 m1 => (w_1, m1) | C0 m1 => (w_0, m1)
                   end
           end
         | Gt =>
           match w_compare yl yh with
             Eq => (w_0, m)
           | Lt => match ww_add_c m (w_mul_c (w_sub xl xh)  (w_sub yh yl)) with
                      C1 m1 => (w_1, m1) | C0 m1 => (w_0, m1)
                   end
           | Gt => (w_0, ww_sub m (w_mul_c (w_sub xl xh)  (w_sub yl yh)))
           end
         end
    | C1 m =>
         match w_compare xl xh with
           Eq => (w_1, m)
         | Lt =>
           match w_compare yl yh with
             Eq => (w_1, m)
           | Lt => match ww_sub_c m (w_mul_c (w_sub xh xl) (w_sub yh yl)) with
                    C0 m1 => (w_1, m1) | C1 m1 => (w_0, m1)
                   end
           | Gt => match ww_add_c m (w_mul_c (w_sub xh xl) (w_sub yl yh)) with
                      C1 m1 => (w_2, m1) | C0 m1 => (w_1, m1)
                   end
           end
         | Gt =>
           match w_compare yl yh with
             Eq => (w_1, m)
           | Lt => match ww_add_c m (w_mul_c (w_sub xl xh) (w_sub yh yl)) with
                      C1 m1 => (w_2, m1) | C0 m1 => (w_1, m1)
                   end
           | Gt => match ww_sub_c m (w_mul_c (w_sub xl xh) (w_sub yl yh)) with
                     C1 m1 => (w_0, m1) | C0 m1 => (w_1, m1)
                   end
           end
         end
    end.

 Definition ww_karatsuba_c :=  double_mul_c kara_prod.

 Definition ww_mul x y :=
  match x, y with
  | W0, _ => W0
  | _, W0 => W0
  | WW xh xl, WW yh yl =>
    let ccl := w_add (w_mul xh yl) (w_mul xl yh) in
    ww_add (w_W0 ccl) (w_mul_c xl yl)
  end.

 Definition ww_square_c x  :=
  match x with
  | W0 => W0
  | WW xh xl =>
    let hh := w_square_c xh in
    let ll := w_square_c xl in
    let xhxl := w_mul_c xh xl in
    let (wc,cc) :=
      match ww_add_c xhxl xhxl with
      | C0 cc => (w_0, cc)
      | C1 cc => (w_1, cc)
      end in
    match cc with
    | W0 => WW (ww_add hh (w_W0 wc)) ll
    | WW cch ccl =>
      match ww_add_c (w_W0 ccl) ll with
      | C0 l => WW (ww_add hh (w_WW wc cch)) l
      | C1 l => WW (ww_add_carry hh (w_WW wc cch)) l
      end
    end
  end.

 Section DoubleMulAddn1.
  Variable w_mul_add : w -> w -> w -> w * w.

  Fixpoint double_mul_add_n1 (n:nat) : word w n -> w -> w -> w * word w n :=
   match n return word w n -> w -> w -> w * word w n with
   | O => w_mul_add
   | S n1 =>
     let mul_add := double_mul_add_n1 n1 in
     fun x y r =>
     match x with
     | W0 => (w_0,extend w_0W n1 r)
     | WW xh xl =>
       let (rl,l) := mul_add xl y r in
       let (rh,h) := mul_add xh y rl in
       (rh, double_WW w_WW n1 h l)
     end
   end.

 End DoubleMulAddn1.

 Section DoubleMulAddmn1.
  Variable wn: Type.
  Variable extend_n : w -> wn.
  Variable wn_0W : wn -> zn2z wn.
  Variable wn_WW : wn -> wn -> zn2z wn.
  Variable w_mul_add_n1 : wn -> w -> w -> w*wn.
  Fixpoint double_mul_add_mn1 (m:nat) :
	word wn m -> w -> w -> w*word wn m :=
   match m return word wn m -> w -> w -> w*word wn m with
   | O => w_mul_add_n1
   | S m1 =>
     let mul_add := double_mul_add_mn1 m1 in
     fun x y r =>
     match x with
     | W0 => (w_0,extend wn_0W m1 (extend_n r))
     | WW xh xl =>
       let (rl,l) := mul_add xl y r in
       let (rh,h) := mul_add xh y rl in
       (rh, double_WW wn_WW m1 h l)
     end
   end.

 End DoubleMulAddmn1.

 Definition w_mul_add x y r :=
  match w_mul_c x y with
  | W0 => (w_0, r)
  | WW h l =>
    match w_add_c l r with
    | C0 lr => (h,lr)
    | C1 lr => (w_succ h, lr)
    end
  end.


 (*Section DoubleProof. *)
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

  Notation "[|| x ||]" :=
    (zn2z_to_Z wwB (ww_to_Z w_digits w_to_Z) x)  (at level 0, x at level 99).

  Notation "[! n | x !]" := (double_to_Z w_digits w_to_Z n x)
    (at level 0, x at level 99).

  Variable spec_more_than_1_digit: 1 < Zpos w_digits.
  Variable spec_w_0   : [|w_0|] = 0.
  Variable spec_w_1   : [|w_1|] = 1.

  Variable spec_to_Z  : forall x, 0 <= [|x|] < wB.

  Variable spec_w_WW : forall h l, [[w_WW h l]] = [|h|] * wB + [|l|].
  Variable spec_w_W0 : forall h, [[w_W0 h]] = [|h|] * wB.
  Variable spec_w_0W : forall l, [[w_0W l]] = [|l|].
  Variable spec_w_compare :
     forall x y, w_compare x y = Z.compare [|x|] [|y|].
  Variable spec_w_succ : forall x, [|w_succ x|] = ([|x|] + 1) mod wB.
  Variable spec_w_add_c  : forall x y, [+|w_add_c x y|] = [|x|] + [|y|].
  Variable spec_w_add : forall x y, [|w_add x y|] = ([|x|] + [|y|]) mod wB.
  Variable spec_w_sub : forall x y, [|w_sub x y|] = ([|x|] - [|y|]) mod wB.

  Variable spec_w_mul_c : forall x y, [[ w_mul_c x y ]] = [|x|] * [|y|].
  Variable spec_w_mul : forall x y, [|w_mul x y|] = ([|x|] * [|y|]) mod wB.
  Variable spec_w_square_c : forall x, [[ w_square_c x]] = [|x|] * [|x|].

  Variable spec_ww_add_c  : forall x y, [+[ww_add_c x y]] = [[x]] + [[y]].
  Variable spec_ww_add : forall x y, [[ww_add x y]] = ([[x]] + [[y]]) mod wwB.
  Variable spec_ww_add_carry :
	 forall x y, [[ww_add_carry x y]] = ([[x]] + [[y]] + 1) mod wwB.
  Variable spec_ww_sub : forall x y, [[ww_sub x y]] = ([[x]] - [[y]]) mod wwB.
  Variable spec_ww_sub_c : forall x y, [-[ww_sub_c x y]] = [[x]] - [[y]].


  Lemma spec_ww_to_Z : forall x, 0 <= [[x]] < wwB.
  Proof. intros x;apply spec_ww_to_Z;auto. Qed.

  Lemma spec_ww_to_Z_wBwB : forall x, 0 <= [[x]] < wB^2.
  Proof. rewrite <- wwB_wBwB;apply spec_ww_to_Z. Qed.

  Hint Resolve spec_ww_to_Z spec_ww_to_Z_wBwB : mult.
  Ltac zarith := auto with zarith mult.

  Lemma wBwB_lex: forall a b c d,
      a * wB^2 + [[b]] <= c * wB^2 + [[d]] ->
      a <= c.
  Proof.
   intros a b c d H; apply beta_lex with [[b]] [[d]] (wB^2);zarith.
  Qed.

  Lemma wBwB_lex_inv: forall a b c d,
      a < c ->
      a * wB^2 + [[b]] < c * wB^2 + [[d]].
  Proof.
   intros a b c d H; apply beta_lex_inv; zarith.
  Qed.

  Lemma sum_mul_carry : forall xh xl yh yl wc cc,
   [|wc|]*wB^2 + [[cc]] = [|xh|] * [|yl|] + [|xl|] * [|yh|] ->
   0 <= [|wc|] <= 1.
  Proof.
   intros.
   apply (sum_mul_carry [|xh|] [|xl|] [|yh|] [|yl|] [|wc|][[cc]] wB);zarith.
   apply wB_pos.
  Qed.

  Theorem mult_add_ineq: forall xH yH crossH,
               0 <= [|xH|] * [|yH|] + [|crossH|] < wwB.
  Proof.
   intros;rewrite wwB_wBwB;apply mult_add_ineq;zarith.
  Qed.

  Hint Resolve mult_add_ineq : mult.

  Lemma spec_mul_aux : forall xh xl yh yl wc (cc:zn2z w) hh ll,
   [[hh]] = [|xh|] * [|yh|] ->
   [[ll]] = [|xl|] * [|yl|] ->
   [|wc|]*wB^2 + [[cc]] = [|xh|] * [|yl|] + [|xl|] * [|yh|] ->
    [||match cc with
      | W0 => WW (ww_add hh (w_W0 wc)) ll
      | WW cch ccl =>
          match ww_add_c (w_W0 ccl) ll with
          | C0 l => WW (ww_add hh (w_WW wc cch)) l
          | C1 l => WW (ww_add_carry hh (w_WW wc cch)) l
          end
      end||] = ([|xh|] * wB + [|xl|]) * ([|yh|] * wB + [|yl|]).
  Proof.
   intros;assert (U1 := wB_pos w_digits).
   replace (([|xh|] * wB + [|xl|]) * ([|yh|] * wB + [|yl|])) with
   ([|xh|]*[|yh|]*wB^2 + ([|xh|]*[|yl|] + [|xl|]*[|yh|])*wB + [|xl|]*[|yl|]).
   2:ring. rewrite <- H1;rewrite <- H;rewrite <- H0.
   assert (H2 := sum_mul_carry _ _ _ _ _ _ H1).
   destruct cc as [ | cch ccl]; simpl zn2z_to_Z; simpl ww_to_Z.
   rewrite spec_ww_add;rewrite spec_w_W0;rewrite Zmod_small;
    rewrite wwB_wBwB. ring.
   rewrite <- (Z.add_0_r ([|wc|]*wB));rewrite H;apply mult_add_ineq3;zarith.
   simpl ww_to_Z in H1. assert (U:=spec_to_Z cch).
   assert ([|wc|]*wB + [|cch|] <= 2*wB - 3).
    destruct (Z_le_gt_dec ([|wc|]*wB + [|cch|]) (2*wB - 3)) as [Hle|Hgt];trivial.
    assert ([|xh|] * [|yl|] + [|xl|] * [|yh|] <= (2*wB - 4)*wB + 2).
     ring_simplify ((2*wB - 4)*wB + 2).
     assert (H4 := Zmult_lt_b _ _ _ (spec_to_Z xh) (spec_to_Z yl)).
     assert (H5 := Zmult_lt_b _ _ _ (spec_to_Z xl) (spec_to_Z yh)).
     omega.
   generalize H3;clear H3;rewrite <- H1.
   rewrite Z.add_assoc; rewrite Z.pow_2_r; rewrite Z.mul_assoc;
     rewrite <- Z.mul_add_distr_r.
    assert (((2 * wB - 4) + 2)*wB <= ([|wc|] * wB + [|cch|])*wB).
     apply Z.mul_le_mono_nonneg;zarith.
    rewrite Z.mul_add_distr_r in H3.
    intros. assert (U2 := spec_to_Z ccl);omega.
   generalize (spec_ww_add_c (w_W0 ccl) ll);destruct (ww_add_c (w_W0 ccl) ll)
   as [l|l];unfold interp_carry;rewrite spec_w_W0;try rewrite Z.mul_1_l;
   simpl zn2z_to_Z;
   try rewrite spec_ww_add;try rewrite spec_ww_add_carry;rewrite spec_w_WW;
   rewrite Zmod_small;rewrite wwB_wBwB;intros.
   rewrite H4;ring. rewrite H;apply mult_add_ineq2;zarith.
   rewrite Z.add_assoc;rewrite Z.mul_add_distr_r.
   rewrite Z.mul_1_l;rewrite <- Z.add_assoc;rewrite H4;ring.
   repeat rewrite <- Z.add_assoc;rewrite H;apply mult_add_ineq2;zarith.
  Qed.

  Lemma spec_double_mul_c : forall cross:w->w->w->w->zn2z w -> zn2z w -> w*zn2z w,
     (forall xh xl yh yl hh ll,
        [[hh]] = [|xh|]*[|yh|] ->
        [[ll]] = [|xl|]*[|yl|] ->
        let (wc,cc) :=  cross xh xl yh yl hh ll in
        [|wc|]*wwB + [[cc]] = [|xh|]*[|yl|] + [|xl|]*[|yh|]) ->
     forall x y, [||double_mul_c cross x y||] = [[x]] * [[y]].
  Proof.
   intros cross Hcross x y;destruct x as [ |xh xl];simpl;trivial.
   destruct y as [ |yh yl];simpl. rewrite Z.mul_0_r;trivial.
   assert (H1:= spec_w_mul_c xh yh);assert (H2:= spec_w_mul_c xl yl).
   generalize (Hcross _ _ _ _ _ _ H1 H2).
   destruct (cross xh xl yh yl (w_mul_c xh yh) (w_mul_c xl yl)) as (wc,cc).
   intros;apply spec_mul_aux;trivial.
   rewrite <- wwB_wBwB;trivial.
  Qed.

  Lemma spec_ww_mul_c : forall x y, [||ww_mul_c x y||] = [[x]] * [[y]].
  Proof.
   intros x y;unfold ww_mul_c;apply spec_double_mul_c.
   intros xh xl yh yl hh ll H1 H2.
   generalize (spec_ww_add_c (w_mul_c xh yl) (w_mul_c xl yh));
   destruct (ww_add_c (w_mul_c xh yl) (w_mul_c xl yh)) as [c|c];
   unfold interp_carry;repeat rewrite spec_w_mul_c;intros H;
   (rewrite spec_w_0 || rewrite spec_w_1);rewrite H;ring.
  Qed.

  Lemma spec_w_2: [|w_2|] = 2.
  unfold w_2; rewrite spec_w_add; rewrite spec_w_1; simpl.
  apply Zmod_small; split; auto with zarith.
  rewrite <- (Z.pow_1_r 2); unfold base; apply Zpower_lt_monotone; auto with zarith.
  Qed.

  Lemma kara_prod_aux : forall xh xl yh yl,
   xh*yh + xl*yl - (xh-xl)*(yh-yl) = xh*yl + xl*yh.
  Proof. intros;ring. Qed.

  Lemma spec_kara_prod : forall xh xl yh yl hh ll,
   [[hh]] = [|xh|]*[|yh|] ->
   [[ll]] = [|xl|]*[|yl|] ->
   let (wc,cc) := kara_prod xh xl yh yl hh ll in
   [|wc|]*wwB + [[cc]] = [|xh|]*[|yl|] + [|xl|]*[|yh|].
  Proof.
   intros xh xl yh yl hh ll H H0; rewrite <- kara_prod_aux;
     rewrite <- H; rewrite <- H0; unfold kara_prod.
   assert (Hxh := (spec_to_Z xh)); assert (Hxl := (spec_to_Z xl));
     assert (Hyh := (spec_to_Z yh)); assert (Hyl := (spec_to_Z yl)).
   generalize (spec_ww_add_c hh ll); case (ww_add_c hh ll);
     intros z Hz; rewrite <- Hz; unfold interp_carry; assert (Hz1 := (spec_ww_to_Z z)).
   rewrite spec_w_compare; case Z.compare_spec; intros Hxlh;
    try rewrite Hxlh; try rewrite spec_w_0; try (ring; fail).
   rewrite spec_w_compare; case Z.compare_spec; intros Hylh.
   rewrite Hylh; rewrite spec_w_0; try (ring; fail).
   rewrite spec_w_0; try (ring; fail).
   repeat (rewrite spec_ww_sub || rewrite spec_w_sub || rewrite spec_w_mul_c).
   repeat rewrite Zmod_small; auto with zarith; try (ring; fail).
   split; auto with zarith.
   simpl in Hz; rewrite Hz; rewrite H; rewrite H0.
   rewrite kara_prod_aux; apply Z.add_nonneg_nonneg; apply Z.mul_nonneg_nonneg; auto with zarith.
   apply Z.le_lt_trans with ([[z]]-0); auto with zarith.
   unfold Z.sub; apply Z.add_le_mono_l; apply Z.le_0_sub; simpl; rewrite Z.opp_involutive.
   apply Z.mul_nonneg_nonneg; auto with zarith.
   match goal with |- context[ww_add_c ?x ?y] =>
     generalize (spec_ww_add_c x y); case (ww_add_c x y); try rewrite spec_w_0;
     intros z1 Hz2
   end.
   simpl in Hz2; rewrite Hz2; repeat (rewrite spec_w_sub || rewrite spec_w_mul_c).
   repeat rewrite Zmod_small; auto with zarith; try (ring; fail).
   rewrite spec_w_1; unfold interp_carry in Hz2; rewrite Hz2;
     repeat (rewrite spec_w_sub || rewrite spec_w_mul_c).
   repeat rewrite Zmod_small; auto with zarith; try (ring; fail).
   rewrite spec_w_compare; case Z.compare_spec; intros Hylh.
   rewrite Hylh; rewrite spec_w_0; try (ring; fail).
   match goal with |- context[ww_add_c ?x ?y] =>
     generalize (spec_ww_add_c x y); case (ww_add_c x y); try rewrite spec_w_0;
     intros z1 Hz2
   end.
   simpl in Hz2; rewrite Hz2; repeat (rewrite spec_w_sub || rewrite spec_w_mul_c).
   repeat rewrite Zmod_small; auto with zarith; try (ring; fail).
   rewrite spec_w_1; unfold interp_carry in Hz2; rewrite Hz2;
     repeat (rewrite spec_w_sub || rewrite spec_w_mul_c).
   repeat rewrite Zmod_small; auto with zarith; try (ring; fail).
   rewrite spec_w_0; try (ring; fail).
   repeat (rewrite spec_ww_sub || rewrite spec_w_sub || rewrite spec_w_mul_c).
   repeat rewrite Zmod_small; auto with zarith; try (ring; fail).
   split.
   match goal with |- context[(?x - ?y) * (?z - ?t)] =>
     replace ((x - y) * (z - t)) with ((y - x) * (t - z)); [idtac | ring]
   end.
   simpl in Hz; rewrite Hz; rewrite H; rewrite H0.
   rewrite kara_prod_aux; apply Z.add_nonneg_nonneg; apply Z.mul_nonneg_nonneg; auto with zarith.
   apply Z.le_lt_trans with ([[z]]-0); auto with zarith.
   unfold Z.sub; apply Z.add_le_mono_l; apply Z.le_0_sub; simpl; rewrite Z.opp_involutive.
   apply Z.mul_nonneg_nonneg; auto with zarith.
   (** there is a carry in hh + ll **)
   rewrite Z.mul_1_l.
   rewrite spec_w_compare; case Z.compare_spec; intros Hxlh;
    try rewrite Hxlh; try rewrite spec_w_1; try (ring; fail).
   rewrite spec_w_compare; case Z.compare_spec; intros Hylh;
     try rewrite Hylh; try rewrite spec_w_1; try (ring; fail).
   match goal with |- context[ww_sub_c ?x ?y] =>
     generalize (spec_ww_sub_c x y); case (ww_sub_c x y); try rewrite spec_w_1;
     intros z1 Hz2
   end.
   simpl in Hz2; rewrite Hz2; repeat (rewrite spec_w_sub || rewrite spec_w_mul_c).
   repeat rewrite Zmod_small; auto with zarith; try (ring; fail).
   rewrite spec_w_0; rewrite Z.mul_0_l; rewrite Z.add_0_l.
   generalize Hz2; clear Hz2; unfold interp_carry.
   repeat (rewrite spec_w_sub || rewrite spec_w_mul_c).
   repeat rewrite Zmod_small; auto with zarith; try (ring; fail).
   match goal with |- context[ww_add_c ?x ?y] =>
     generalize (spec_ww_add_c x y); case (ww_add_c x y); try rewrite spec_w_1;
     intros z1 Hz2
   end.
   simpl in Hz2; rewrite Hz2; repeat (rewrite spec_w_sub || rewrite spec_w_mul_c).
   repeat rewrite Zmod_small; auto with zarith; try (ring; fail).
   rewrite spec_w_2; unfold interp_carry in Hz2.
   transitivity (wwB + (1 * wwB + [[z1]])).
   ring.
   rewrite Hz2; repeat (rewrite spec_w_sub || rewrite spec_w_mul_c).
   repeat rewrite Zmod_small; auto with zarith; try (ring; fail).
   rewrite spec_w_compare; case Z.compare_spec; intros Hylh;
     try rewrite Hylh; try rewrite spec_w_1; try (ring; fail).
   match goal with |- context[ww_add_c ?x ?y] =>
     generalize (spec_ww_add_c x y); case (ww_add_c x y); try rewrite spec_w_1;
     intros z1 Hz2
   end.
   simpl in Hz2; rewrite Hz2; repeat (rewrite spec_w_sub || rewrite spec_w_mul_c).
   repeat rewrite Zmod_small; auto with zarith; try (ring; fail).
   rewrite spec_w_2; unfold interp_carry in Hz2.
   transitivity (wwB + (1 * wwB + [[z1]])).
   ring.
   rewrite Hz2; repeat (rewrite spec_w_sub || rewrite spec_w_mul_c).
   repeat rewrite Zmod_small; auto with zarith; try (ring; fail).
   match goal with |- context[ww_sub_c ?x ?y] =>
     generalize (spec_ww_sub_c x y); case (ww_sub_c x y); try rewrite spec_w_1;
     intros z1 Hz2
   end.
   simpl in Hz2; rewrite Hz2; repeat (rewrite spec_w_sub || rewrite spec_w_mul_c).
   repeat rewrite Zmod_small; auto with zarith; try (ring; fail).
   rewrite spec_w_0; rewrite Z.mul_0_l; rewrite Z.add_0_l.
   match goal with |- context[(?x - ?y) * (?z - ?t)] =>
     replace ((x - y) * (z - t)) with ((y - x) * (t - z)); [idtac | ring]
   end.
   generalize Hz2; clear Hz2; unfold interp_carry.
   repeat (rewrite spec_w_sub || rewrite spec_w_mul_c).
   repeat rewrite Zmod_small; auto with zarith; try (ring; fail).
  Qed.

  Lemma sub_carry : forall xh xl yh yl z,
    0 <= z ->
    [|xh|]*[|yl|] + [|xl|]*[|yh|] = wwB + z ->
    z < wwB.
  Proof.
   intros xh xl yh yl z Hle Heq.
   destruct (Z_le_gt_dec wwB z);auto with zarith.
   generalize (Zmult_lt_b _ _ _ (spec_to_Z xh) (spec_to_Z yl)).
   generalize (Zmult_lt_b _ _ _ (spec_to_Z xl) (spec_to_Z yh)).
   rewrite <- wwB_wBwB;intros H1 H2.
   assert (H3 := wB_pos w_digits).
   assert (2*wB <= wwB).
    rewrite wwB_wBwB; rewrite Z.pow_2_r; apply Z.mul_le_mono_nonneg;zarith.
   omega.
  Qed.

  Ltac Spec_ww_to_Z x :=
   let H:= fresh "H" in
   assert (H:= spec_ww_to_Z x).

  Ltac Zmult_lt_b x y :=
   let H := fresh "H" in
   assert (H := Zmult_lt_b _ _ _ (spec_to_Z x) (spec_to_Z y)).

  Lemma spec_ww_karatsuba_c : forall x y, [||ww_karatsuba_c x y||]=[[x]]*[[y]].
  Proof.
   intros x y; unfold ww_karatsuba_c;apply spec_double_mul_c.
   intros; apply spec_kara_prod; auto.
  Qed.

  Lemma spec_ww_mul : forall x y, [[ww_mul x y]] = [[x]]*[[y]] mod wwB.
  Proof.
   assert (U:= lt_0_wB w_digits).
   assert (U1:= lt_0_wwB w_digits).
   intros x y; case x; auto; intros xh xl.
   case y; auto.
   simpl; rewrite Z.mul_0_r; rewrite Zmod_small; auto with zarith.
   intros yh yl;simpl.
   repeat (rewrite spec_ww_add || rewrite spec_w_W0 || rewrite spec_w_mul_c
    || rewrite spec_w_add || rewrite spec_w_mul).
   rewrite <- Zplus_mod; auto with zarith.
   repeat (rewrite Z.mul_add_distr_r || rewrite Z.mul_add_distr_l).
   rewrite <- Zmult_mod_distr_r; auto with zarith.
   rewrite <- Z.pow_2_r; rewrite <- wwB_wBwB; auto with zarith.
   rewrite Zplus_mod; auto with zarith.
   rewrite Zmod_mod; auto with zarith.
   rewrite <- Zplus_mod; auto with zarith.
   match goal with |- ?X mod _ = _ =>
     rewrite <- Z_mod_plus with (a := X) (b := [|xh|] * [|yh|])
   end; auto with zarith.
   f_equal; auto; rewrite wwB_wBwB; ring.
  Qed.

  Lemma spec_ww_square_c : forall x, [||ww_square_c x||] = [[x]]*[[x]].
  Proof.
   destruct x as [ |xh xl];simpl;trivial.
   case_eq match ww_add_c (w_mul_c xh xl) (w_mul_c xh xl) with
          | C0 cc => (w_0, cc)
          | C1 cc => (w_1, cc)
          end;intros wc cc Heq.
   apply (spec_mul_aux xh xl xh xl wc cc);trivial.
   generalize Heq (spec_ww_add_c (w_mul_c xh xl) (w_mul_c xh xl));clear Heq.
   rewrite spec_w_mul_c;destruct (ww_add_c (w_mul_c xh xl) (w_mul_c xh xl));
   unfold interp_carry;try rewrite Z.mul_1_l;intros Heq Heq';inversion Heq;
   rewrite (Z.mul_comm [|xl|]);subst.
   rewrite spec_w_0;rewrite Z.mul_0_l;rewrite Z.add_0_l;trivial.
   rewrite spec_w_1;rewrite Z.mul_1_l;rewrite <- wwB_wBwB;trivial.
  Qed.

  Section DoubleMulAddn1Proof.

   Variable w_mul_add : w -> w -> w -> w * w.
   Variable spec_w_mul_add : forall x y r,
    let (h,l):= w_mul_add x y r in
    [|h|]*wB+[|l|] = [|x|]*[|y|] + [|r|].

   Lemma spec_double_mul_add_n1 : forall n x y r,
     let (h,l) := double_mul_add_n1 w_mul_add n x y r in
     [|h|]*double_wB w_digits n + [!n|l!] = [!n|x!]*[|y|]+[|r|].
   Proof.
    induction n;intros x y r;trivial.
    exact (spec_w_mul_add x y r).
    unfold double_mul_add_n1;destruct x as[ |xh xl];
     fold(double_mul_add_n1 w_mul_add).
    rewrite spec_w_0;rewrite spec_extend;simpl;trivial.
    assert(H:=IHn xl y r);destruct (double_mul_add_n1 w_mul_add n xl y r)as(rl,l).
   assert(U:=IHn xh y rl);destruct(double_mul_add_n1 w_mul_add n xh y rl)as(rh,h).
    rewrite <- double_wB_wwB. rewrite spec_double_WW;simpl;trivial.
    rewrite Z.mul_add_distr_r;rewrite <- Z.add_assoc;rewrite <- H.
    rewrite Z.mul_assoc;rewrite Z.add_assoc;rewrite <- Z.mul_add_distr_r.
    rewrite U;ring.
   Qed.

  End DoubleMulAddn1Proof.

  Lemma spec_w_mul_add : forall x y r,
    let (h,l):= w_mul_add x y r in
    [|h|]*wB+[|l|] = [|x|]*[|y|] + [|r|].
  Proof.
   intros x y r;unfold w_mul_add;assert (H:=spec_w_mul_c x y);
   destruct (w_mul_c x y) as [ |h l];simpl;rewrite <- H.
   rewrite spec_w_0;trivial.
   assert (U:=spec_w_add_c l r);destruct (w_add_c l r) as [lr|lr];unfold
   interp_carry in U;try rewrite Z.mul_1_l in H;simpl.
   rewrite U;ring. rewrite spec_w_succ. rewrite Zmod_small.
   rewrite <- Z.add_assoc;rewrite <- U;ring.
   simpl in H;assert (H1:= Zmult_lt_b _ _ _ (spec_to_Z x) (spec_to_Z y)).
   rewrite <- H in H1.
   assert (H2:=spec_to_Z h);split;zarith.
   case H1;clear H1;intro H1;clear H1.
   replace (wB ^ 2 - 2 * wB) with ((wB - 2)*wB). 2:ring.
   intros H0;assert (U1:= wB_pos w_digits).
   assert (H1 := beta_lex _ _ _ _ _ H0 (spec_to_Z l));zarith.
  Qed.

(* End DoubleProof. *)

End DoubleMul.

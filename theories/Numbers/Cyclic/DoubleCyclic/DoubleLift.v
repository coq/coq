(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

(*i $Id$ i*)

Set Implicit Arguments.

Require Import ZArith.
Require Import BigNumPrelude.
Require Import DoubleType.
Require Import DoubleBase.

Open Local Scope Z_scope.

Section DoubleLift.
 Variable w : Set.
 Variable w_0 : w.
 Variable w_WW : w -> w -> zn2z w.
 Variable w_W0 : w ->  zn2z w.
 Variable w_0W : w ->  zn2z w.
 Variable w_compare : w -> w -> comparison.
 Variable ww_compare : zn2z w -> zn2z w -> comparison.
 Variable w_head0 : w -> w.
 Variable w_tail0 : w -> w.
 Variable w_add: w -> w -> zn2z w.
 Variable w_add_mul_div : w -> w -> w -> w.
 Variable ww_sub: zn2z w -> zn2z w -> zn2z w.
 Variable w_digits : positive.
 Variable ww_Digits : positive.
 Variable w_zdigits : w.
 Variable ww_zdigits : zn2z w.
 Variable low: zn2z w -> w.

 Definition ww_head0 x :=
  match x with
  | W0 => ww_zdigits
  | WW xh xl =>
    match w_compare w_0 xh with
    | Eq => w_add w_zdigits (w_head0 xl)
    | _ => w_0W (w_head0 xh)
    end
  end.


 Definition ww_tail0 x :=
  match x with
  | W0 => ww_zdigits
  | WW xh xl =>
    match w_compare w_0 xl with
    | Eq => w_add w_zdigits (w_tail0 xh)
    | _ => w_0W (w_tail0 xl)
    end
  end.


  (* 0 < p < ww_digits *)
 Definition ww_add_mul_div p x y := 
  let zdigits := w_0W w_zdigits in
  match x, y with
  | W0, W0 => W0
  | W0, WW yh yl =>
    match ww_compare p zdigits with
    | Eq => w_0W yh 
    | Lt => w_0W (w_add_mul_div (low p) w_0 yh)
    | Gt =>
      let n := low (ww_sub p zdigits) in
      w_WW (w_add_mul_div n w_0 yh) (w_add_mul_div n yh yl)
    end
  | WW xh xl, W0 =>
    match ww_compare p zdigits with
    | Eq => w_W0 xl 
    | Lt => w_WW (w_add_mul_div (low p) xh xl) (w_add_mul_div (low p) xl w_0)
    | Gt =>
      let n := low (ww_sub p zdigits) in
      w_W0 (w_add_mul_div n xl w_0) 
    end
  | WW xh xl, WW yh yl =>
    match ww_compare p zdigits with
    | Eq => w_WW xl yh 
    | Lt => w_WW (w_add_mul_div (low p) xh xl) (w_add_mul_div (low p) xl yh)
    | Gt =>
      let n := low (ww_sub p zdigits) in
      w_WW (w_add_mul_div n xl yh) (w_add_mul_div n yh yl)
    end
  end.

 Section DoubleProof.
  Variable w_to_Z : w -> Z.
 
  Notation wB  := (base w_digits).
  Notation wwB := (base (ww_digits w_digits)).
  Notation "[| x |]" := (w_to_Z x)  (at level 0, x at level 99).
  Notation "[[ x ]]" := (ww_to_Z w_digits w_to_Z x)(at level 0, x at level 99).

  Variable spec_w_0   : [|w_0|] = 0.
  Variable spec_to_Z  : forall x, 0 <= [|x|] < wB.
  Variable spec_to_w_Z  : forall x, 0 <= [[x]] < wwB.
  Variable spec_w_WW : forall h l, [[w_WW h l]] = [|h|] * wB + [|l|].
  Variable spec_w_W0 : forall h, [[w_W0 h]] = [|h|] * wB.
  Variable spec_w_0W : forall l, [[w_0W l]] = [|l|].
  Variable spec_compare : forall x y,
       match w_compare x y with
       | Eq => [|x|] = [|y|]
       | Lt => [|x|] < [|y|]
       | Gt => [|x|] > [|y|]
       end.
  Variable spec_ww_compare : forall x y,
       match ww_compare x y with
       | Eq => [[x]] = [[y]]
       | Lt => [[x]] < [[y]]
       | Gt => [[x]] > [[y]]
       end.
  Variable spec_ww_digits : ww_Digits = xO w_digits.
  Variable spec_w_head00  : forall x, [|x|] = 0 -> [|w_head0 x|] = Zpos w_digits.
  Variable spec_w_head0  : forall x,  0 < [|x|] ->
	 wB/ 2 <= 2 ^ ([|w_head0 x|]) * [|x|] < wB.
  Variable spec_w_tail00  : forall x, [|x|] = 0 -> [|w_tail0 x|] = Zpos w_digits.
  Variable spec_w_tail0 : forall x, 0 < [|x|] -> 
         exists y, 0 <= y /\ [|x|] = (2* y + 1) * (2 ^ [|w_tail0 x|]).
  Variable spec_w_add_mul_div : forall x y p,
       [|p|] <= Zpos w_digits ->
       [| w_add_mul_div p x y |] =
         ([|x|] * (2 ^ [|p|]) +
          [|y|] / (2 ^ ((Zpos w_digits) - [|p|]))) mod wB.
 Variable spec_w_add: forall x y, 
   [[w_add x y]] = [|x|] + [|y|].
 Variable spec_ww_sub: forall x y, 
   [[ww_sub x y]] = ([[x]] - [[y]]) mod wwB.

 Variable spec_zdigits : [| w_zdigits |] = Zpos w_digits.
 Variable spec_low: forall x, [| low x|] = [[x]] mod wB.
 
 Variable spec_ww_zdigits : [[ww_zdigits]] = Zpos ww_Digits.

  Hint Resolve div_le_0 div_lt w_to_Z_wwB: lift.
  Ltac zarith := auto with zarith lift.

  Lemma spec_ww_head00  : forall x, [[x]] = 0 -> [[ww_head0 x]] = Zpos ww_Digits.
  Proof.
  intros x; case x; unfold ww_head0.
    intros HH; rewrite spec_ww_zdigits; auto.
  intros xh xl; simpl; intros Hx.
  case (spec_to_Z xh); intros Hx1 Hx2.
  case (spec_to_Z xl); intros Hy1 Hy2.
  assert (F1: [|xh|] = 0).
    case (Zle_lt_or_eq _ _ Hy1); auto; intros Hy3.
    absurd (0 < [|xh|] * wB + [|xl|]); auto with zarith.
    apply Zlt_le_trans with (1 := Hy3); auto with zarith.
    pattern [|xl|] at 1; rewrite <- (Zplus_0_l [|xl|]).
    apply Zplus_le_compat_r; auto with zarith.
    case (Zle_lt_or_eq _ _ Hx1); auto; intros Hx3.
    absurd (0 < [|xh|] * wB + [|xl|]); auto with zarith.
    rewrite <- Hy3; rewrite Zplus_0_r; auto with zarith.
    apply Zmult_lt_0_compat; auto with zarith.
  generalize (spec_compare w_0 xh); case w_compare.
    intros H; simpl.
    rewrite spec_w_add; rewrite spec_w_head00.
    rewrite spec_zdigits; rewrite spec_ww_digits.
    rewrite Zpos_xO; auto with zarith.
  rewrite F1 in Hx; auto with zarith.
  rewrite spec_w_0; auto with zarith.
  rewrite spec_w_0; auto with zarith.
  Qed.
   
  Lemma spec_ww_head0  : forall x,  0 < [[x]] ->
	 wwB/ 2 <= 2 ^ [[ww_head0 x]] * [[x]] < wwB.
  Proof.
   clear spec_ww_zdigits.
   rewrite wwB_div_2;rewrite Zmult_comm;rewrite wwB_wBwB.
   assert (U:= lt_0_wB w_digits); destruct x as [ |xh xl];simpl ww_to_Z;intros H.
   unfold Zlt in H;discriminate H.
   assert (H0 := spec_compare w_0 xh);rewrite spec_w_0 in H0.
   destruct (w_compare w_0 xh).
   rewrite <- H0. simpl Zplus. rewrite <- H0 in H;simpl in H.
   case (spec_to_Z w_zdigits); 
     case (spec_to_Z (w_head0 xl)); intros HH1 HH2 HH3 HH4.
   rewrite spec_w_add.
   rewrite spec_zdigits; rewrite Zpower_exp; auto with zarith.
   case (spec_w_head0 H); intros H1 H2.
   rewrite Zpower_2; fold wB; rewrite <- Zmult_assoc; split.
     apply Zmult_le_compat_l; auto with zarith.
   apply Zmult_lt_compat_l; auto with zarith.
   assert (H1 := spec_w_head0 H0).
   rewrite spec_w_0W.
   split.
   rewrite Zmult_plus_distr_r;rewrite Zmult_assoc.
   apply Zle_trans with (2 ^ [|w_head0 xh|] * [|xh|] * wB).
   rewrite Zmult_comm; zarith.
   assert (0 <= 2 ^ [|w_head0 xh|] * [|xl|]);zarith.
   assert (H2:=spec_to_Z xl);apply Zmult_le_0_compat;zarith.
   case (spec_to_Z (w_head0 xh)); intros H2 _.
   generalize ([|w_head0 xh|]) H1 H2;clear H1 H2;
     intros p H1 H2.
   assert (Eq1 : 2^p < wB).
     rewrite <- (Zmult_1_r (2^p));apply Zle_lt_trans with (2^p*[|xh|]);zarith.
   assert (Eq2: p < Zpos w_digits).
    destruct (Zle_or_lt (Zpos w_digits) p);trivial;contradict  Eq1.
   apply Zle_not_lt;unfold base;apply Zpower_le_monotone;zarith.
   assert (Zpos w_digits = p + (Zpos w_digits - p)). ring.
   rewrite Zpower_2.
   unfold base at 2;rewrite H3;rewrite Zpower_exp;zarith.
   rewrite <- Zmult_assoc; apply Zmult_lt_compat_l; zarith.
   rewrite <- (Zplus_0_r (2^(Zpos w_digits - p)*wB));apply beta_lex_inv;zarith.
   apply Zmult_lt_reg_r with (2 ^ p); zarith.
   rewrite <- Zpower_exp;zarith. 
   rewrite Zmult_comm;ring_simplify (Zpos w_digits - p + p);fold wB;zarith.
   assert (H1 := spec_to_Z xh);zarith.
  Qed.

  Lemma spec_ww_tail00  : forall x, [[x]] = 0 -> [[ww_tail0 x]] = Zpos ww_Digits.
  Proof.
  intros x; case x; unfold ww_tail0.
    intros HH; rewrite spec_ww_zdigits; auto.
  intros xh xl; simpl; intros Hx.
  case (spec_to_Z xh); intros Hx1 Hx2.
  case (spec_to_Z xl); intros Hy1 Hy2.
  assert (F1: [|xh|] = 0).
    case (Zle_lt_or_eq _ _ Hy1); auto; intros Hy3.
    absurd (0 < [|xh|] * wB + [|xl|]); auto with zarith.
    apply Zlt_le_trans with (1 := Hy3); auto with zarith.
    pattern [|xl|] at 1; rewrite <- (Zplus_0_l [|xl|]).
    apply Zplus_le_compat_r; auto with zarith.
    case (Zle_lt_or_eq _ _ Hx1); auto; intros Hx3.
    absurd (0 < [|xh|] * wB + [|xl|]); auto with zarith.
    rewrite <- Hy3; rewrite Zplus_0_r; auto with zarith.
    apply Zmult_lt_0_compat; auto with zarith.
  assert (F2: [|xl|] = 0).
    rewrite F1 in Hx; auto with zarith.
  generalize (spec_compare w_0 xl); case w_compare.
    intros H; simpl.
    rewrite spec_w_add; rewrite spec_w_tail00; auto.
    rewrite spec_zdigits; rewrite spec_ww_digits.
    rewrite Zpos_xO; auto with zarith.
  rewrite spec_w_0; auto with zarith.
  rewrite spec_w_0; auto with zarith.
  Qed.

  Lemma spec_ww_tail0  : forall x,  0 < [[x]] ->
	 exists y, 0 <= y /\ [[x]] = (2 * y + 1) * 2 ^ [[ww_tail0 x]].
  Proof.
   clear spec_ww_zdigits.
   destruct x as [ |xh xl];simpl ww_to_Z;intros H.
   unfold Zlt in H;discriminate H.
   assert (H0 := spec_compare w_0 xl);rewrite spec_w_0 in H0.
   destruct (w_compare w_0 xl).
   rewrite <- H0; rewrite Zplus_0_r.
   case (spec_to_Z (w_tail0 xh)); intros HH1 HH2.
   generalize H; rewrite <- H0; rewrite Zplus_0_r; clear H; intros H.
   case (@spec_w_tail0 xh).
     apply Zmult_lt_reg_r with wB; auto with zarith.
     unfold base; auto with zarith.
   intros z (Hz1, Hz2); exists z; split; auto.
   rewrite spec_w_add; rewrite (fun x => Zplus_comm [|x|]).
   rewrite spec_zdigits; rewrite Zpower_exp; auto with zarith.
   rewrite Zmult_assoc; rewrite <- Hz2; auto.

   case (spec_to_Z (w_tail0 xh)); intros HH1 HH2.
   case (spec_w_tail0 H0); intros z (Hz1, Hz2).
   assert (Hp: [|w_tail0 xl|] < Zpos w_digits).
     case (Zle_or_lt (Zpos w_digits) [|w_tail0 xl|]); auto; intros H1.
     absurd (2 ^  (Zpos w_digits) <= 2 ^ [|w_tail0 xl|]).
       apply Zlt_not_le.
       case (spec_to_Z xl); intros HH3 HH4.
       apply Zle_lt_trans with (2 := HH4).
       apply Zle_trans with (1 * 2 ^ [|w_tail0 xl|]); auto with zarith.
       rewrite Hz2.
       apply Zmult_le_compat_r; auto with zarith.
     apply Zpower_le_monotone; auto with zarith.
   exists ([|xh|] * (2 ^ ((Zpos w_digits - [|w_tail0 xl|]) - 1)) + z); split.
     apply Zplus_le_0_compat; auto.
     apply Zmult_le_0_compat; auto with zarith.
     case (spec_to_Z xh); auto.
   rewrite spec_w_0W.
   rewrite (Zmult_plus_distr_r 2); rewrite <- Zplus_assoc.
   rewrite Zmult_plus_distr_l; rewrite <- Hz2.
   apply f_equal2 with (f := Zplus); auto.
   rewrite (Zmult_comm 2).
   repeat rewrite <- Zmult_assoc.
   apply f_equal2 with (f := Zmult); auto.
   case (spec_to_Z (w_tail0 xl)); intros HH3 HH4.
   pattern 2 at 2; rewrite <- Zpower_1_r.
   lazy beta; repeat rewrite <- Zpower_exp; auto with zarith.
   unfold base; apply f_equal with (f := Zpower 2); auto with zarith.

   contradict H0; case (spec_to_Z xl); auto with zarith.
  Qed.

  Hint Rewrite Zdiv_0_l Zmult_0_l Zplus_0_l Zmult_0_r Zplus_0_r
    spec_w_W0 spec_w_0W spec_w_WW spec_w_0  
    (wB_div w_digits w_to_Z spec_to_Z) 
    (wB_div_plus w_digits w_to_Z spec_to_Z) : w_rewrite.
  Ltac w_rewrite := autorewrite with w_rewrite;trivial.

  Lemma spec_ww_add_mul_div_aux : forall xh xl yh yl p,
   let zdigits := w_0W w_zdigits in
    [[p]] <= Zpos (xO w_digits) ->
      [[match ww_compare p zdigits with
        | Eq => w_WW xl yh
        | Lt => w_WW (w_add_mul_div (low p) xh xl) 
                     (w_add_mul_div (low p) xl yh)
        | Gt =>
              let n := low (ww_sub p zdigits) in
            w_WW (w_add_mul_div n xl yh) (w_add_mul_div n yh yl)
        end]] =  
      ([[WW xh xl]] * (2^[[p]]) +
       [[WW yh yl]] / (2^(Zpos (xO w_digits) - [[p]]))) mod wwB.
  Proof.
   clear spec_ww_zdigits.
   intros xh xl yh yl p zdigits;assert (HwwB := wwB_pos w_digits).
   case (spec_to_w_Z p); intros Hv1 Hv2.
   replace (Zpos (xO w_digits)) with (Zpos w_digits + Zpos w_digits).
   2 : rewrite Zpos_xO;ring.
   replace (Zpos w_digits + Zpos w_digits - [[p]]) with 
     (Zpos w_digits + (Zpos w_digits - [[p]])). 2:ring.
   intros Hp; assert (Hxh := spec_to_Z xh);assert (Hxl:=spec_to_Z xl);
   assert (Hx := spec_ww_to_Z w_digits w_to_Z spec_to_Z (WW xh xl));
   simpl in Hx;assert (Hyh := spec_to_Z yh);assert (Hyl:=spec_to_Z yl);
   assert (Hy:=spec_ww_to_Z w_digits w_to_Z spec_to_Z (WW yh yl));simpl in Hy.
   generalize (spec_ww_compare p zdigits); case ww_compare; intros H1.
   rewrite H1; unfold zdigits; rewrite spec_w_0W.
   rewrite spec_zdigits; rewrite Zminus_diag; rewrite Zplus_0_r.
   simpl ww_to_Z; w_rewrite;zarith.
   fold wB.
   rewrite Zmult_plus_distr_l;rewrite <- Zmult_assoc;rewrite <- Zplus_assoc.
   rewrite <- Zpower_2.
   rewrite <- wwB_wBwB;apply Zmod_unique with [|xh|]. 
   exact (spec_ww_to_Z w_digits w_to_Z spec_to_Z (WW xl yh)). ring.
   simpl ww_to_Z; w_rewrite;zarith.
   assert (HH0: [|low p|] = [[p]]).
     rewrite spec_low.
     apply Zmod_small.
     case (spec_to_w_Z p); intros HH1 HH2; split; auto.
     generalize H1; unfold zdigits; rewrite spec_w_0W;
      rewrite spec_zdigits; intros tmp.
     apply Zlt_le_trans with (1 := tmp).
     unfold base.
     apply Zpower2_le_lin; auto with zarith.
   2: generalize H1; unfold zdigits; rewrite spec_w_0W;
      rewrite spec_zdigits; auto with zarith.
   generalize H1; unfold zdigits; rewrite spec_w_0W;
      rewrite spec_zdigits; auto; clear H1; intros H1.
   assert (HH: [|low p|] <= Zpos w_digits).
     rewrite HH0; auto with zarith.
   repeat rewrite spec_w_add_mul_div with (1 := HH).
   rewrite HH0.
   rewrite Zmult_plus_distr_l.
   pattern ([|xl|] * 2 ^ [[p]]) at 2;
   rewrite shift_unshift_mod with (n:= Zpos w_digits);fold wB;zarith.
   replace ([|xh|] * wB * 2^[[p]]) with ([|xh|] * 2^[[p]] * wB). 2:ring. 
   rewrite Zplus_assoc;rewrite <- Zmult_plus_distr_l. rewrite <- Zplus_assoc.
   unfold base at 5;rewrite <- Zmod_shift_r;zarith.
   unfold base;rewrite Zmod_shift_r with (b:= Zpos (ww_digits w_digits));
   fold wB;fold wwB;zarith.
   rewrite wwB_wBwB;rewrite Zpower_2; rewrite  Zmult_mod_distr_r;zarith.
   unfold ww_digits;rewrite Zpos_xO;zarith. apply Z_mod_lt;zarith.
   split;zarith. apply Zdiv_lt_upper_bound;zarith.
   rewrite <- Zpower_exp;zarith.
   ring_simplify ([[p]] + (Zpos w_digits - [[p]]));fold wB;zarith.
   assert (Hv: [[p]] > Zpos w_digits).
     generalize H1; clear H1.
     unfold zdigits; rewrite spec_w_0W; rewrite spec_zdigits; auto.
   clear H1.
   assert (HH0: [|low (ww_sub p zdigits)|] = [[p]] - Zpos w_digits).
     rewrite spec_low.
     rewrite spec_ww_sub.
     unfold zdigits; rewrite spec_w_0W; rewrite spec_zdigits.
     rewrite <- Zmod_div_mod; auto with zarith.
     rewrite Zmod_small; auto with zarith.
     split; auto with zarith.
     apply Zle_lt_trans with (Zpos w_digits); auto with zarith.
     unfold base; apply Zpower2_lt_lin; auto with zarith.
     exists wB; unfold base.
     unfold ww_digits; rewrite (Zpos_xO w_digits).
     rewrite <- Zpower_exp; auto with zarith.
     apply f_equal with (f := fun x => 2 ^ x); auto with zarith.
   assert (HH: [|low (ww_sub p zdigits)|] <= Zpos w_digits).
     rewrite HH0; auto with zarith.
   replace (Zpos w_digits + (Zpos w_digits - [[p]])) with
       (Zpos w_digits - ([[p]] - Zpos w_digits)); zarith.
   lazy zeta; simpl ww_to_Z; w_rewrite;zarith.
   repeat rewrite spec_w_add_mul_div;zarith.
   rewrite HH0.
   pattern wB at 5;replace wB with 
    (2^(([[p]] - Zpos w_digits) 
         + (Zpos w_digits - ([[p]] - Zpos w_digits)))).
   rewrite Zpower_exp;zarith. rewrite Zmult_assoc.
   rewrite Z_div_plus_l;zarith.
   rewrite shift_unshift_mod with (a:= [|yh|]) (p:= [[p]] - Zpos w_digits)
    (n := Zpos w_digits);zarith. fold wB.
   set (u := [[p]] - Zpos w_digits).
   replace [[p]] with (u + Zpos w_digits);zarith.
   rewrite Zpower_exp;zarith. rewrite Zmult_assoc. fold wB.
   repeat rewrite Zplus_assoc. rewrite <- Zmult_plus_distr_l.
   repeat rewrite <- Zplus_assoc.
   unfold base;rewrite Zmod_shift_r with (b:= Zpos (ww_digits w_digits));
   fold wB;fold wwB;zarith.
   unfold base;rewrite Zmod_shift_r with (a:= Zpos w_digits) 
   (b:= Zpos w_digits);fold wB;fold wwB;zarith.
   rewrite wwB_wBwB; rewrite Zpower_2; rewrite  Zmult_mod_distr_r;zarith.
   rewrite Zmult_plus_distr_l.
   replace ([|xh|] * wB * 2 ^ u) with 
     ([|xh|]*2^u*wB). 2:ring.
   repeat rewrite <- Zplus_assoc. 
   rewrite (Zplus_comm ([|xh|] * 2 ^ u * wB)).
   rewrite Z_mod_plus;zarith. rewrite Z_mod_mult;zarith.
   unfold base;rewrite <- Zmod_shift_r;zarith. fold base;apply Z_mod_lt;zarith.
   unfold u; split;zarith. 
   split;zarith. unfold u; apply Zdiv_lt_upper_bound;zarith.
   rewrite <- Zpower_exp;zarith.
   fold u. 
   ring_simplify (u + (Zpos w_digits - u)); fold 
   wB;zarith. unfold ww_digits;rewrite Zpos_xO;zarith.
   unfold base;rewrite <- Zmod_shift_r;zarith. fold base;apply Z_mod_lt;zarith.
   unfold u; split;zarith.
   unfold u; split;zarith.
   apply Zdiv_lt_upper_bound;zarith.
   rewrite <- Zpower_exp;zarith.
   fold u. 
   ring_simplify (u + (Zpos w_digits - u)); fold wB; auto with zarith.
   unfold u;zarith.
   unfold u;zarith.
   set (u := [[p]] - Zpos w_digits).
   ring_simplify (u + (Zpos w_digits - u)); fold wB; auto with zarith.
  Qed.

  Lemma spec_ww_add_mul_div : forall x y p,
       [[p]] <= Zpos (xO w_digits) ->
       [[ ww_add_mul_div p x y ]] =
         ([[x]] * (2^[[p]]) +
          [[y]] / (2^(Zpos (xO w_digits) - [[p]]))) mod wwB.
  Proof.
   clear spec_ww_zdigits.
   intros x y p H.
   destruct x as [ |xh xl];
   [assert (H1 := @spec_ww_add_mul_div_aux w_0 w_0)
   |assert (H1 := @spec_ww_add_mul_div_aux xh xl)];
   (destruct y as [ |yh yl];
    [generalize (H1 w_0 w_0 p H) | generalize (H1 yh yl p H)];
    clear H1;w_rewrite);simpl ww_add_mul_div.
   replace [[WW w_0 w_0]] with 0;[w_rewrite|simpl;w_rewrite;trivial].
   intros Heq;rewrite <- Heq;clear Heq; auto.
   generalize (spec_ww_compare p (w_0W w_zdigits)); 
     case ww_compare; intros H1; w_rewrite.
   rewrite (spec_w_add_mul_div w_0 w_0);w_rewrite;zarith.
   generalize H1; w_rewrite; rewrite spec_zdigits; clear H1; intros H1.
   assert (HH0: [|low p|] = [[p]]).
     rewrite spec_low.
     apply Zmod_small.
     case (spec_to_w_Z p); intros HH1 HH2; split; auto.
     apply Zlt_le_trans with (1 := H1).
     unfold base; apply Zpower2_le_lin; auto with zarith.
   rewrite HH0; auto with zarith.
   replace [[WW w_0 w_0]] with 0;[w_rewrite|simpl;w_rewrite;trivial].
   intros Heq;rewrite <- Heq;clear Heq.
   generalize (spec_ww_compare p (w_0W w_zdigits)); 
     case ww_compare; intros H1; w_rewrite.
   rewrite (spec_w_add_mul_div w_0 w_0);w_rewrite;zarith.
   rewrite Zpos_xO in H;zarith.
   assert (HH: [|low (ww_sub p (w_0W w_zdigits)) |] = [[p]] - Zpos w_digits).
     generalize H1; clear H1.
     rewrite spec_low.
     rewrite spec_ww_sub; w_rewrite; intros H1.
     rewrite <- Zmod_div_mod; auto with zarith.
     rewrite Zmod_small; auto with zarith.
     split; auto with zarith.
     apply Zle_lt_trans with (Zpos w_digits); auto with zarith.
     unfold base; apply Zpower2_lt_lin; auto with zarith.
     unfold base; auto with zarith.
     unfold base; auto with zarith.
     exists wB; unfold base.
     unfold ww_digits; rewrite (Zpos_xO w_digits).
     rewrite <- Zpower_exp; auto with zarith.
     apply f_equal with (f := fun x => 2 ^ x); auto with zarith.
  case (spec_to_Z xh); auto with zarith.
  Qed.

 End DoubleProof.

End DoubleLift.


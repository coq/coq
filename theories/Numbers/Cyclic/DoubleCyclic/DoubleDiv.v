(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*         Benjamin Gregoire, Laurent Thery, INRIA, 2007                *)
(************************************************************************)

Set Implicit Arguments.

Require Import ZArith.
Require Import BigNumPrelude.
Require Import DoubleType.
Require Import DoubleBase.
Require Import DoubleDivn1.
Require Import DoubleAdd.
Require Import DoubleSub.

Local Open Scope Z_scope.

Ltac zarith := auto with zarith.


Section POS_MOD.

 Variable w:Type.
 Variable w_0 : w.
 Variable w_digits : positive.
 Variable w_zdigits : w.
 Variable w_WW : w -> w -> zn2z w.
 Variable w_pos_mod : w -> w -> w.
 Variable w_compare : w -> w -> comparison.
 Variable ww_compare : zn2z w -> zn2z w -> comparison.
 Variable w_0W : w ->  zn2z w.
 Variable low: zn2z w -> w.
 Variable ww_sub: zn2z w -> zn2z w -> zn2z w.
 Variable ww_zdigits : zn2z w.


 Definition ww_pos_mod p x :=
  let zdigits := w_0W w_zdigits in
  match x with
  | W0 => W0
  | WW xh xl =>
    match ww_compare p zdigits with
    | Eq => w_WW w_0 xl
    | Lt => w_WW w_0 (w_pos_mod (low p) xl)
    | Gt =>
      match ww_compare p ww_zdigits with
      | Lt =>
        let n := low (ww_sub p zdigits) in
        w_WW (w_pos_mod n xh) xl
      | _ => x
      end
    end
  end.


  Variable w_to_Z : w -> Z.

  Notation wB  := (base w_digits).
  Notation wwB := (base (ww_digits w_digits)).
  Notation "[| x |]" := (w_to_Z x)  (at level 0, x at level 99).

  Notation "[[ x ]]" := (ww_to_Z w_digits w_to_Z x)(at level 0, x at level 99).


  Variable spec_w_0   : [|w_0|] = 0.

  Variable spec_to_Z  : forall x, 0 <= [|x|] < wB.

  Variable spec_to_w_Z  : forall x, 0 <= [[x]] < wwB.

  Variable spec_w_WW : forall h l, [[w_WW h l]] = [|h|] * wB + [|l|].

  Variable spec_pos_mod : forall w p,
       [|w_pos_mod p w|] = [|w|] mod (2 ^ [|p|]).

  Variable spec_w_0W : forall l, [[w_0W l]] = [|l|].
  Variable spec_ww_compare : forall x y,
    ww_compare x y = Z.compare [[x]] [[y]].
 Variable spec_ww_sub: forall x y,
   [[ww_sub x y]] = ([[x]] - [[y]]) mod wwB.

 Variable spec_zdigits : [| w_zdigits |] = Zpos w_digits.
 Variable spec_low: forall x, [| low x|] = [[x]] mod wB.
 Variable spec_ww_zdigits : [[ww_zdigits]] = 2 * [|w_zdigits|].
 Variable spec_ww_digits : ww_digits w_digits = xO w_digits.


  Hint Rewrite spec_w_0 spec_w_WW : w_rewrite.

 Lemma spec_ww_pos_mod : forall w p,
       [[ww_pos_mod p w]] = [[w]] mod (2 ^ [[p]]).
 assert (HHHHH:= lt_0_wB w_digits).
 assert (F0: forall x y, x - y + y = x); auto with zarith.
 intros w1 p; case (spec_to_w_Z p); intros HH1 HH2.
 unfold ww_pos_mod; case w1. reflexivity.
 intros xh xl; rewrite spec_ww_compare.
    case Z.compare_spec;
    rewrite spec_w_0W; rewrite spec_zdigits; fold wB;
    intros H1.
   rewrite H1; simpl ww_to_Z.
   autorewrite with w_rewrite rm10.
   rewrite Zplus_mod; auto with zarith.
   rewrite Z_mod_mult; auto with zarith.
   autorewrite with rm10.
   rewrite Zmod_mod; auto with zarith.
   rewrite Zmod_small; auto with zarith.
   autorewrite with w_rewrite rm10.
   simpl ww_to_Z.
   rewrite spec_pos_mod.
   assert (HH0: [|low p|] = [[p]]).
     rewrite spec_low.
     apply Zmod_small; auto with zarith.
     case (spec_to_w_Z p); intros HHH1 HHH2; split; auto with zarith.
     apply Z.lt_le_trans with (1 := H1).
     unfold base; apply Zpower2_le_lin; auto with zarith.
   rewrite HH0.
   rewrite Zplus_mod; auto with zarith.
   unfold base.
   rewrite <- (F0 (Zpos w_digits) [[p]]).
   rewrite Zpower_exp; auto with zarith.
   rewrite Z.mul_assoc.
   rewrite Z_mod_mult; auto with zarith.
   autorewrite with w_rewrite rm10.
   rewrite Zmod_mod; auto with zarith.
  rewrite spec_ww_compare.
    case Z.compare_spec; rewrite spec_ww_zdigits;
                     rewrite spec_zdigits; intros H2.
  replace (2^[[p]]) with wwB.
    rewrite Zmod_small; auto with zarith.
  unfold base; rewrite H2.
  rewrite spec_ww_digits; auto.
  assert (HH0: [|low (ww_sub p (w_0W w_zdigits))|] =
         [[p]] - Zpos w_digits).
    rewrite spec_low.
    rewrite spec_ww_sub.
    rewrite spec_w_0W; rewrite spec_zdigits.
    rewrite <- Zmod_div_mod; auto with zarith.
    rewrite Zmod_small; auto with zarith.
    split; auto with zarith.
    apply Z.lt_le_trans with (Zpos w_digits); auto with zarith.
    unfold base; apply Zpower2_le_lin; auto with zarith.
    exists wB; unfold base; rewrite <- Zpower_exp; auto with zarith.
    rewrite spec_ww_digits;
      apply f_equal with (f := Z.pow 2); rewrite Pos2Z.inj_xO; auto with zarith.
   simpl ww_to_Z; autorewrite with w_rewrite.
   rewrite spec_pos_mod; rewrite HH0.
   pattern [|xh|] at 2;
     rewrite Z_div_mod_eq with (b := 2 ^ ([[p]] - Zpos w_digits));
     auto with zarith.
   rewrite (fun x => (Z.mul_comm (2 ^ x))); rewrite Z.mul_add_distr_r.
   unfold base; rewrite <- Z.mul_assoc; rewrite <- Zpower_exp;
    auto with zarith.
   rewrite F0; auto with zarith.
   rewrite <- Z.add_assoc; rewrite Zplus_mod; auto with zarith.
   rewrite Z_mod_mult; auto with zarith.
   autorewrite with rm10.
   rewrite Zmod_mod; auto with zarith.
   symmetry; apply Zmod_small; auto with zarith.
   case (spec_to_Z xh); intros U1 U2.
   case (spec_to_Z xl); intros U3 U4.
   split; auto with zarith.
   apply Z.add_nonneg_nonneg; auto with zarith.
   apply Z.mul_nonneg_nonneg; auto with zarith.
   match goal with |- 0 <= ?X mod ?Y =>
    case (Z_mod_lt X Y); auto with zarith
   end.
   match goal with |- ?X mod ?Y * ?U + ?Z < ?T =>
    apply Z.le_lt_trans with ((Y - 1) * U + Z );
     [case (Z_mod_lt X Y); auto with zarith | idtac]
   end.
   match goal with |- ?X * ?U + ?Y < ?Z =>
    apply Z.le_lt_trans with (X * U + (U - 1))
   end.
   apply Z.add_le_mono_l; auto with zarith.
   case (spec_to_Z xl); unfold base; auto with zarith.
   rewrite Z.mul_sub_distr_r; rewrite <- Zpower_exp; auto with zarith.
   rewrite F0; auto with zarith.
  rewrite Zmod_small; auto with zarith.
  case (spec_to_w_Z (WW xh xl)); intros U1 U2.
  split; auto with zarith.
  apply Z.lt_le_trans with (1:= U2).
  unfold base; rewrite spec_ww_digits.
  apply Zpower_le_monotone; auto with zarith.
  split; auto with zarith.
  rewrite Pos2Z.inj_xO; auto with zarith.
 Qed.

End POS_MOD.

Section DoubleDiv32.

 Variable w             : Type.
 Variable w_0           : w.
 Variable w_Bm1         : w.
 Variable w_Bm2         : w.
 Variable w_WW          : w -> w -> zn2z w.
 Variable w_compare     : w -> w -> comparison.
 Variable w_add_c       : w -> w -> carry w.
 Variable w_add_carry_c : w -> w -> carry w.
 Variable w_add         : w -> w -> w.
 Variable w_add_carry   : w -> w -> w.
 Variable w_pred        : w -> w.
 Variable w_sub         : w -> w -> w.
 Variable w_mul_c       : w -> w -> zn2z w.
 Variable w_div21       : w -> w -> w -> w*w.
 Variable ww_sub_c      : zn2z w -> zn2z w -> carry (zn2z w).

 Definition w_div32_body a1 a2 a3 b1 b2 :=
  match w_compare a1 b1 with
  | Lt =>
    let (q,r) := w_div21 a1 a2 b1 in
    match ww_sub_c (w_WW r a3) (w_mul_c q b2) with
    | C0 r1 => (q,r1)
    | C1 r1 =>
      let q := w_pred q in
      ww_add_c_cont w_WW w_add_c w_add_carry_c
      (fun r2=>(w_pred q, ww_add w_add_c w_add w_add_carry r2 (WW b1 b2)))
      (fun r2 => (q,r2))
      r1 (WW b1 b2)
    end
  | Eq =>
    ww_add_c_cont w_WW w_add_c w_add_carry_c
    (fun r => (w_Bm2, ww_add w_add_c w_add w_add_carry r (WW b1 b2)))
    (fun r => (w_Bm1,r))
    (WW (w_sub a2 b2) a3) (WW b1 b2)
  | Gt => (w_0, W0) (* cas absurde *)
  end.

 Definition w_div32 a1 a2 a3 b1 b2 :=
  Eval lazy beta iota delta [ww_add_c_cont ww_add w_div32_body] in
     w_div32_body a1 a2 a3 b1 b2.

 (* Proof *)

  Variable w_digits      : positive.
  Variable w_to_Z : w -> Z.

  Notation wB  := (base w_digits).
  Notation wwB := (base (ww_digits w_digits)).
  Notation "[| x |]" := (w_to_Z x)  (at level 0, x at level 99).
  Notation "[+| c |]" :=
   (interp_carry 1 wB w_to_Z c) (at level 0, c at level 99).
  Notation "[-| c |]" :=
   (interp_carry (-1) wB w_to_Z c) (at level 0, c at level 99).

  Notation "[[ x ]]" := (ww_to_Z w_digits w_to_Z x)(at level 0, x at level 99).
  Notation "[-[ c ]]" :=
   (interp_carry (-1) wwB (ww_to_Z w_digits w_to_Z) c)
   (at level 0, c at level 99).


  Variable spec_w_0   : [|w_0|] = 0.
  Variable spec_w_Bm1   : [|w_Bm1|] = wB - 1.
  Variable spec_w_Bm2   : [|w_Bm2|] = wB - 2.

  Variable spec_to_Z  : forall x, 0 <= [|x|] < wB.

  Variable spec_w_WW : forall h l, [[w_WW h l]] = [|h|] * wB + [|l|].
  Variable spec_compare :
     forall x y, w_compare x y = Z.compare [|x|] [|y|].
  Variable spec_w_add_c  : forall x y, [+|w_add_c x y|] = [|x|] + [|y|].
  Variable spec_w_add_carry_c :
         forall x y, [+|w_add_carry_c x y|] = [|x|] + [|y|] + 1.

  Variable spec_w_add : forall x y, [|w_add x y|] = ([|x|] + [|y|]) mod wB.
  Variable spec_w_add_carry :
	 forall x y, [|w_add_carry x y|] = ([|x|] + [|y|] + 1) mod wB.

  Variable spec_pred : forall x, [|w_pred x|] = ([|x|] - 1) mod wB.
  Variable spec_sub : forall x y, [|w_sub x y|] = ([|x|] - [|y|]) mod wB.

  Variable spec_mul_c : forall x y, [[ w_mul_c x y ]] = [|x|] * [|y|].
  Variable spec_div21 : forall a1 a2 b,
      wB/2 <= [|b|] ->
      [|a1|] < [|b|] ->
      let (q,r) := w_div21 a1 a2 b in
      [|a1|] *wB+ [|a2|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|].

  Variable spec_ww_sub_c : forall x y, [-[ww_sub_c x y]] = [[x]] - [[y]].

  Ltac Spec_w_to_Z x :=
   let H:= fresh "HH" in
   assert (H:= spec_to_Z x).
  Ltac Spec_ww_to_Z x :=
   let H:= fresh "HH" in
   assert (H:= spec_ww_to_Z w_digits w_to_Z spec_to_Z x).

  Theorem wB_div2: forall x, wB/2  <= x -> wB <= 2 * x.
   intros x H; rewrite <- wB_div_2; apply Z.mul_le_mono_nonneg_l; auto with zarith.
  Qed.

  Lemma Zmult_lt_0_reg_r_2 : forall n m : Z, 0 <= n -> 0 < m * n -> 0 < m.
  Proof.
   intros n m H1 H2;apply Z.mul_pos_cancel_r with n;trivial.
   Z.le_elim H1; trivial.
   subst;rewrite Z.mul_0_r in H2;discriminate H2.
  Qed.

  Theorem spec_w_div32 : forall a1 a2 a3 b1 b2,
     wB/2 <= [|b1|] ->
     [[WW a1 a2]] < [[WW b1 b2]] ->
     let (q,r) := w_div32 a1 a2 a3 b1 b2 in
     [|a1|] * wwB + [|a2|] * wB  + [|a3|] =
        [|q|] *  ([|b1|] * wB + [|b2|])  + [[r]] /\
     0 <= [[r]] < [|b1|] * wB + [|b2|].
  Proof.
   intros a1 a2 a3 b1 b2 Hle Hlt.
   assert (U:= lt_0_wB w_digits); assert (U1:= lt_0_wwB w_digits).
   Spec_w_to_Z a1;Spec_w_to_Z a2;Spec_w_to_Z a3;Spec_w_to_Z b1;Spec_w_to_Z b2.
   rewrite wwB_wBwB; rewrite Z.pow_2_r; rewrite Z.mul_assoc;rewrite <- Z.mul_add_distr_r.
   change (w_div32 a1 a2 a3 b1 b2) with (w_div32_body a1 a2 a3 b1 b2).
   unfold w_div32_body.
   rewrite spec_compare. case Z.compare_spec; intro Hcmp.
   simpl in Hlt.
   rewrite Hcmp in Hlt;assert ([|a2|] < [|b2|]). omega.
   assert ([[WW (w_sub a2 b2) a3]] = ([|a2|]-[|b2|])*wB + [|a3|] + wwB).
    simpl;rewrite spec_sub.
    assert ([|a2|] - [|b2|] = wB*(-1) + ([|a2|] - [|b2|] + wB)). ring.
    assert (0 <= [|a2|] - [|b2|] + wB < wB). omega.
    rewrite <-(Zmod_unique ([|a2|]-[|b2|]) wB (-1) ([|a2|]-[|b2|]+wB) H1 H0).
    rewrite wwB_wBwB;ring.
   assert (U2 := wB_pos w_digits).
   eapply spec_ww_add_c_cont with (P :=
     fun (x y:zn2z w) (res:w*zn2z w) =>
     let (q, r) := res in
     ([|a1|] * wB + [|a2|]) * wB + [|a3|] =
     [|q|] * ([|b1|] * wB + [|b2|]) + [[r]] /\
     0 <= [[r]] < [|b1|] * wB + [|b2|]);eauto.
   rewrite H0;intros r.
   repeat
    (rewrite spec_ww_add;eauto || rewrite spec_w_Bm1 || rewrite spec_w_Bm2);
   simpl ww_to_Z;try rewrite Z.mul_1_l;intros H1.
   assert (0<= ([[r]] + ([|b1|] * wB + [|b2|])) - wwB < [|b1|] * wB + [|b2|]).
   Spec_ww_to_Z r;split;zarith.
   rewrite H1.
   assert (H12:= wB_div2 Hle). assert (wwB <= 2 * [|b1|] * wB).
   rewrite wwB_wBwB; rewrite Z.pow_2_r; zarith.
   assert (-wwB < ([|a2|] - [|b2|]) * wB + [|a3|] < 0).
   split. apply Z.lt_le_trans with (([|a2|] - [|b2|]) * wB);zarith.
   rewrite wwB_wBwB;replace (-(wB^2)) with (-wB*wB);[zarith | ring].
   apply Z.mul_lt_mono_pos_r;zarith.
   apply Z.le_lt_trans with (([|a2|] - [|b2|]) * wB + (wB -1));zarith.
   replace ( ([|a2|] - [|b2|]) * wB + (wB - 1)) with
     (([|a2|] - [|b2|] + 1) * wB + - 1);[zarith | ring].
   assert (([|a2|] - [|b2|] + 1) * wB <= 0);zarith.
   replace 0 with (0*wB);zarith.
   replace (([|a2|] - [|b2|]) * wB + [|a3|] + wwB + ([|b1|] * wB + [|b2|]) +
              ([|b1|] * wB + [|b2|]) - wwB) with
         (([|a2|] - [|b2|]) * wB + [|a3|] + 2*[|b1|] * wB + 2*[|b2|]);
   [zarith | ring].
   rewrite <- (Zmod_unique ([[r]] + ([|b1|] * wB + [|b2|])) wwB
             1 ([[r]] + ([|b1|] * wB + [|b2|]) - wwB));zarith;try (ring;fail).
   split. rewrite H1;rewrite Hcmp;ring. trivial.
   Spec_ww_to_Z (WW b1 b2). simpl in HH4;zarith.
   rewrite H0;intros r;repeat
    (rewrite spec_w_Bm1 || rewrite spec_w_Bm2);
   simpl ww_to_Z;try rewrite Z.mul_1_l;intros H1.
   assert ([[r]]=([|a2|]-[|b2|])*wB+[|a3|]+([|b1|]*wB+[|b2|])). zarith.
   split. rewrite H2;rewrite Hcmp;ring.
   split. Spec_ww_to_Z r;zarith.
   rewrite H2.
   assert (([|a2|] - [|b2|]) * wB + [|a3|] < 0);zarith.
   apply Z.le_lt_trans with (([|a2|] - [|b2|]) * wB + (wB -1));zarith.
   replace ( ([|a2|] - [|b2|]) * wB + (wB - 1)) with
     (([|a2|] - [|b2|] + 1) * wB + - 1);[zarith|ring].
   assert (([|a2|] - [|b2|] + 1) * wB <= 0);zarith.
   replace 0 with (0*wB);zarith.
   (* Cas Lt *)
   assert (Hdiv21 := spec_div21 a2 Hle Hcmp);
    destruct (w_div21 a1 a2 b1) as (q, r);destruct Hdiv21.
   rewrite H.
   assert (Hq := spec_to_Z q).
   generalize
    (spec_ww_sub_c (w_WW r a3) (w_mul_c q b2));
    destruct (ww_sub_c (w_WW r a3) (w_mul_c q b2))
    as [r1|r1];repeat (rewrite spec_w_WW || rewrite spec_mul_c);
    unfold interp_carry;intros H1.
    rewrite H1.
   split. ring. split.
   rewrite <- H1;destruct (spec_ww_to_Z w_digits w_to_Z spec_to_Z r1);trivial.
   apply Z.le_lt_trans with ([|r|] * wB + [|a3|]).
   assert ( 0 <= [|q|] * [|b2|]);zarith.
   apply beta_lex_inv;zarith.
   assert ([[r1]] = [|r|] * wB + [|a3|] - [|q|] * [|b2|] + wwB).
   rewrite <- H1;ring.
   Spec_ww_to_Z r1; assert (0 <= [|r|]*wB). zarith.
   assert (0 < [|q|] * [|b2|]). zarith.
   assert (0 < [|q|]).
    apply Zmult_lt_0_reg_r_2 with [|b2|];zarith.
   eapply spec_ww_add_c_cont with (P :=
     fun (x y:zn2z w) (res:w*zn2z w) =>
     let (q0, r0) := res in
      ([|q|] * [|b1|] + [|r|]) * wB + [|a3|] =
      [|q0|] * ([|b1|] * wB + [|b2|]) + [[r0]] /\
      0 <= [[r0]] < [|b1|] * wB + [|b2|]);eauto.
   intros r2;repeat (rewrite spec_pred || rewrite spec_ww_add;eauto);
   simpl ww_to_Z;intros H7.
   assert (0 < [|q|] - 1).
   assert (H6 : 1 <= [|q|]) by zarith.
   Z.le_elim H6;zarith.
   rewrite <- H6 in H2;rewrite H2 in H7.
   assert (0 < [|b1|]*wB). apply Z.mul_pos_pos;zarith.
   Spec_ww_to_Z r2. zarith.
   rewrite (Zmod_small ([|q|] -1));zarith.
   rewrite (Zmod_small ([|q|] -1 -1));zarith.
   assert ([[r2]] + ([|b1|] * wB + [|b2|]) =
       wwB * 1 +
       ([|r|] * wB + [|a3|] - [|q|] * [|b2|] + 2 * ([|b1|] * wB + [|b2|]))).
   rewrite H7;rewrite H2;ring.
   assert
    ([|r|]*wB + [|a3|] - [|q|]*[|b2|] + 2 * ([|b1|]*wB + [|b2|])
        < [|b1|]*wB + [|b2|]).
   Spec_ww_to_Z r2;omega.
   Spec_ww_to_Z (WW b1 b2). simpl in HH5.
   assert
    (0 <= [|r|]*wB + [|a3|] - [|q|]*[|b2|] + 2 * ([|b1|]*wB + [|b2|])
       < wwB). split;try omega.
   replace (2*([|b1|]*wB+[|b2|])) with ((2*[|b1|])*wB+2*[|b2|]). 2:ring.
   assert (H12:= wB_div2 Hle). assert (wwB <= 2 * [|b1|] * wB).
   rewrite wwB_wBwB; rewrite Z.pow_2_r; zarith. omega.
   rewrite <- (Zmod_unique
            ([[r2]] + ([|b1|] * wB + [|b2|]))
            wwB
            1
            ([|r|] * wB + [|a3|] - [|q|] * [|b2|] + 2*([|b1|] * wB + [|b2|]))
            H10 H8).
   split. ring. zarith.
   intros r2;repeat (rewrite spec_pred);simpl ww_to_Z;intros H7.
   rewrite (Zmod_small ([|q|] -1));zarith.
   split.
   replace [[r2]] with  ([[r1]] + ([|b1|] * wB + [|b2|]) -wwB).
   rewrite H2; ring. rewrite <- H7; ring.
   Spec_ww_to_Z r2;Spec_ww_to_Z r1. omega.
   simpl in Hlt.
   assert ([|a1|] * wB + [|a2|] <= [|b1|] * wB + [|b2|]). zarith.
   assert (H1 := beta_lex _ _ _ _ _ H HH0 HH3). rewrite spec_w_0;simpl;zarith.
  Qed.


End DoubleDiv32.

Section DoubleDiv21.
 Variable w : Type.
 Variable w_0 : w.

 Variable w_0W : w -> zn2z w.
 Variable w_div32 : w -> w -> w -> w -> w -> w * zn2z w.

 Variable ww_1 : zn2z w.
 Variable ww_compare : zn2z w -> zn2z w -> comparison.
 Variable ww_sub : zn2z w -> zn2z w -> zn2z w.


 Definition ww_div21 a1 a2 b :=
  match a1 with
  | W0 =>
    match ww_compare a2 b with
    | Gt => (ww_1, ww_sub a2 b)
    | Eq => (ww_1, W0)
    | Lt => (W0, a2)
    end
  | WW a1h a1l =>
    match a2 with
    | W0 =>
      match b with
      | W0 => (W0,W0) (* cas absurde *)
      | WW b1 b2 =>
        let (q1, r)  := w_div32 a1h a1l w_0 b1 b2 in
        match r with
        | W0 => (WW q1 w_0, W0)
        | WW r1 r2 =>
	  let (q2, s)  := w_div32 r1 r2 w_0 b1 b2 in
          (WW q1 q2, s)
        end
      end
    | WW a2h a2l =>
      match b with
      | W0 => (W0,W0) (* cas absurde *)
      | WW b1 b2 =>
        let (q1, r)  := w_div32 a1h a1l a2h b1 b2 in
        match r with
        | W0 => (WW q1 w_0, w_0W a2l)
        | WW r1 r2 =>
	  let (q2, s)  := w_div32 r1 r2 a2l b1 b2 in
          (WW q1 q2, s)
        end
      end
    end
  end.

 (* Proof *)

  Variable w_digits : positive.
  Variable w_to_Z : w -> Z.
  Notation wB  := (base w_digits).
  Notation wwB := (base (ww_digits w_digits)).
  Notation "[| x |]" := (w_to_Z x)  (at level 0, x at level 99).
  Notation "[[ x ]]" := (ww_to_Z w_digits w_to_Z x)(at level 0, x at level 99).
  Notation "[-[ c ]]" :=
   (interp_carry (-1) wwB (ww_to_Z w_digits w_to_Z) c)
   (at level 0, c at level 99).

  Variable spec_w_0   : [|w_0|] = 0.
  Variable spec_to_Z  : forall x, 0 <= [|x|] < wB.
  Variable spec_w_0W : forall l, [[w_0W l]] = [|l|].
  Variable spec_w_div32 : forall a1 a2 a3 b1 b2,
     wB/2 <= [|b1|] ->
     [[WW a1 a2]] < [[WW b1 b2]] ->
     let (q,r) := w_div32 a1 a2 a3 b1 b2 in
     [|a1|] * wwB + [|a2|] * wB  + [|a3|] =
        [|q|] *  ([|b1|] * wB + [|b2|])  + [[r]] /\
     0 <= [[r]] < [|b1|] * wB + [|b2|].
  Variable spec_ww_1 : [[ww_1]] = 1.
  Variable spec_ww_compare :  forall x y,
    ww_compare x y = Z.compare [[x]] [[y]].
  Variable spec_ww_sub : forall x y, [[ww_sub x y]] = ([[x]] - [[y]]) mod wwB.

  Theorem wwB_div: wwB  = 2 * (wwB / 2).
  Proof.
   rewrite wwB_div_2; rewrite  Z.mul_assoc; rewrite  wB_div_2; auto.
   rewrite <- Z.pow_2_r; apply wwB_wBwB.
  Qed.

  Ltac Spec_w_to_Z x :=
   let H:= fresh "HH" in
   assert (H:= spec_to_Z x).
  Ltac Spec_ww_to_Z x :=
   let H:= fresh "HH" in
   assert (H:= spec_ww_to_Z w_digits w_to_Z spec_to_Z x).

  Theorem   spec_ww_div21 : forall a1 a2 b,
     wwB/2 <= [[b]] ->
     [[a1]] < [[b]] ->
     let (q,r) := ww_div21 a1 a2 b in
     [[a1]] *wwB+[[a2]] = [[q]] *  [[b]] + [[r]] /\ 0 <= [[r]] < [[b]].
  Proof.
   assert (U:= lt_0_wB w_digits).
   assert (U1:= lt_0_wwB w_digits).
   intros a1 a2 b H Hlt; unfold ww_div21.
   Spec_ww_to_Z b; assert (Eq: 0 < [[b]]).    Spec_ww_to_Z a1;omega.
   generalize Hlt H ;clear Hlt H;case a1.
   intros H1 H2;simpl in H1;Spec_ww_to_Z a2.
   rewrite spec_ww_compare. case Z.compare_spec;
   simpl;try rewrite spec_ww_1;autorewrite with rm10; intros;zarith.
   rewrite spec_ww_sub;simpl. rewrite Zmod_small;zarith.
   split. ring.
   assert (wwB <= 2*[[b]]);zarith.
   rewrite wwB_div;zarith.
   intros a1h a1l.  Spec_w_to_Z a1h;Spec_w_to_Z a1l. Spec_ww_to_Z a2.
   destruct a2 as [ |a3 a4];
    (destruct b as [ |b1 b2];[unfold Z.le in Eq;discriminate Eq|idtac]);
   try (Spec_w_to_Z a3; Spec_w_to_Z a4); Spec_w_to_Z b1; Spec_w_to_Z b2;
   intros Hlt H;  match goal with |-context [w_div32 ?X ?Y ?Z ?T ?U] =>
     generalize (@spec_w_div32 X Y Z T U); case (w_div32 X Y Z T U);
     intros q1 r H0
   end; (assert (Eq1: wB / 2 <= [|b1|]);[
    apply (@beta_lex (wB / 2) 0 [|b1|] [|b2|] wB); auto with zarith;
    autorewrite with rm10;repeat rewrite (Z.mul_comm wB);
    rewrite <- wwB_div_2; trivial
   | generalize (H0 Eq1 Hlt);clear H0;destruct r as [ |r1 r2];simpl;
     try rewrite spec_w_0; try rewrite spec_w_0W;repeat rewrite Z.add_0_r;
     intros (H1,H2) ]).
   split;[rewrite wwB_wBwB; rewrite Z.pow_2_r | trivial].
   rewrite Z.mul_assoc;rewrite Z.mul_add_distr_r;rewrite <- Z.mul_assoc;
   rewrite <- Z.pow_2_r; rewrite <- wwB_wBwB;rewrite H1;ring.
   destruct H2 as (H2,H3);match goal with |-context [w_div32 ?X ?Y ?Z ?T ?U] =>
     generalize (@spec_w_div32 X Y Z T U); case (w_div32 X Y Z T U);
     intros q r H0;generalize (H0 Eq1 H3);clear H0;intros (H4,H5) end.
   split;[rewrite wwB_wBwB | trivial].
   rewrite Z.pow_2_r.
   rewrite Z.mul_assoc;rewrite Z.mul_add_distr_r;rewrite <- Z.mul_assoc;
   rewrite <- Z.pow_2_r.
   rewrite <- wwB_wBwB;rewrite H1.
   rewrite spec_w_0 in H4;rewrite Z.add_0_r in H4.
   repeat rewrite Z.mul_add_distr_r. rewrite <- (Z.mul_assoc [|r1|]).
   rewrite <- Z.pow_2_r; rewrite <- wwB_wBwB;rewrite H4;simpl;ring.
   split;[rewrite wwB_wBwB | split;zarith].
   replace (([|a1h|] * wB + [|a1l|]) * wB^2 + ([|a3|] * wB + [|a4|]))
   with (([|a1h|] * wwB + [|a1l|] * wB + [|a3|])*wB+ [|a4|]).
   rewrite H1;ring. rewrite wwB_wBwB;ring.
   change [|a4|] with (0*wB+[|a4|]);apply beta_lex_inv;zarith.
   assert (1 <= wB/2);zarith.
    assert (H_:= wB_pos w_digits);apply Zdiv_le_lower_bound;zarith.
   destruct H2 as (H2,H3);match goal with |-context [w_div32 ?X ?Y ?Z ?T ?U] =>
     generalize (@spec_w_div32 X Y Z T U); case (w_div32 X Y Z T U);
     intros q r H0;generalize (H0 Eq1 H3);clear H0;intros (H4,H5) end.
   split;trivial.
   replace (([|a1h|] * wB + [|a1l|]) * wwB + ([|a3|] * wB + [|a4|])) with
   (([|a1h|] * wwB + [|a1l|] * wB + [|a3|])*wB + [|a4|]);
   [rewrite H1 | rewrite wwB_wBwB;ring].
   replace (([|q1|]*([|b1|]*wB+[|b2|])+([|r1|]*wB+[|r2|]))*wB+[|a4|]) with
   (([|q1|]*([|b1|]*wB+[|b2|]))*wB+([|r1|]*wwB+[|r2|]*wB+[|a4|]));
   [rewrite H4;simpl|rewrite wwB_wBwB];ring.
  Qed.

End DoubleDiv21.

Section DoubleDivGt.
 Variable w : Type.
 Variable w_digits : positive.
 Variable w_0 : w.

 Variable w_WW : w -> w -> zn2z w.
 Variable w_0W : w -> zn2z w.
 Variable w_compare : w -> w -> comparison.
 Variable w_eq0 : w -> bool.
 Variable w_opp_c : w -> carry w.
 Variable w_opp w_opp_carry : w -> w.
 Variable w_sub_c : w -> w -> carry w.
 Variable w_sub w_sub_carry : w -> w -> w.

 Variable w_div_gt : w -> w -> w*w.
 Variable w_mod_gt : w -> w -> w.
 Variable w_gcd_gt : w -> w -> w.
 Variable w_add_mul_div : w -> w -> w -> w.
 Variable w_head0 : w -> w.
 Variable w_div21 : w -> w -> w -> w * w.
 Variable w_div32 : w -> w -> w -> w -> w -> w * zn2z w.


 Variable _ww_zdigits : zn2z w.
 Variable ww_1 : zn2z w.
 Variable ww_add_mul_div : zn2z w -> zn2z w -> zn2z w -> zn2z w.

 Variable w_zdigits : w.

 Definition ww_div_gt_aux ah al bh bl :=
  Eval lazy beta iota delta [ww_sub ww_opp] in
    let p := w_head0 bh in
    match w_compare p w_0 with
    | Gt =>
      let b1 := w_add_mul_div p bh bl in
      let b2 := w_add_mul_div p bl w_0 in
      let a1 := w_add_mul_div p w_0 ah in
      let a2 := w_add_mul_div p ah al in
      let a3 := w_add_mul_div p al w_0 in
      let (q,r) := w_div32 a1 a2 a3 b1 b2 in
      (WW w_0 q, ww_add_mul_div
        (ww_sub w_0 w_WW w_opp_c w_opp_carry w_sub_c
            w_opp w_sub w_sub_carry _ww_zdigits (w_0W p)) W0 r)
    | _ => (ww_1, ww_sub w_0 w_WW w_opp_c w_opp_carry w_sub_c
            w_opp w_sub w_sub_carry (WW ah al) (WW bh bl))
    end.

 Definition ww_div_gt a b :=
  Eval lazy beta iota delta [ww_div_gt_aux double_divn1
  double_divn1_p double_divn1_p_aux double_divn1_0 double_divn1_0_aux
  double_split double_0 double_WW] in
  match a, b with
  | W0, _ => (W0,W0)
  | _, W0 => (W0,W0)
  | WW ah al, WW bh bl =>
    if w_eq0 ah then
     let (q,r) := w_div_gt al bl in
     (WW w_0 q, w_0W r)
    else
     match w_compare w_0 bh with
     | Eq =>
       let(q,r):=
        double_divn1 w_zdigits w_0 w_WW w_head0 w_add_mul_div w_div21
                  w_compare w_sub 1 a bl in
       (q, w_0W r)
     | Lt => ww_div_gt_aux ah al bh bl
     | Gt => (W0,W0) (* cas absurde *)
     end
  end.

 Definition ww_mod_gt_aux ah al bh bl :=
  Eval lazy beta iota delta [ww_sub ww_opp] in
    let p := w_head0 bh in
    match w_compare p w_0 with
    | Gt =>
      let b1 := w_add_mul_div p bh bl in
      let b2 := w_add_mul_div p bl w_0 in
      let a1 := w_add_mul_div p w_0 ah in
      let a2 := w_add_mul_div p ah al in
      let a3 := w_add_mul_div p al w_0 in
      let (q,r) := w_div32 a1 a2 a3 b1 b2 in
      ww_add_mul_div (ww_sub w_0 w_WW w_opp_c w_opp_carry w_sub_c
         w_opp w_sub w_sub_carry _ww_zdigits (w_0W p)) W0 r
    | _ =>
      ww_sub w_0 w_WW w_opp_c w_opp_carry w_sub_c
         w_opp w_sub w_sub_carry (WW ah al) (WW bh bl)
    end.

 Definition ww_mod_gt a b :=
  Eval lazy beta iota delta [ww_mod_gt_aux double_modn1
  double_modn1_p double_modn1_p_aux double_modn1_0 double_modn1_0_aux
  double_split double_0 double_WW snd] in
  match a, b with
  | W0, _ => W0
  | _, W0 => W0
  | WW ah al, WW bh bl =>
    if w_eq0 ah then w_0W (w_mod_gt al bl)
    else
     match w_compare w_0 bh with
     | Eq =>
       w_0W (double_modn1 w_zdigits w_0 w_head0 w_add_mul_div w_div21
             w_compare w_sub 1 a bl)
     | Lt => ww_mod_gt_aux ah al bh bl
     | Gt => W0 (* cas absurde *)
     end
  end.

  Definition ww_gcd_gt_body (cont: w->w->w->w->zn2z w) (ah al bh bl: w) :=
   Eval lazy beta iota delta [ww_mod_gt_aux double_modn1
   double_modn1_p double_modn1_p_aux double_modn1_0 double_modn1_0_aux
   double_split double_0 double_WW snd] in
    match w_compare w_0 bh with
    | Eq =>
      match w_compare w_0 bl with
      | Eq => WW ah al (* normalement n'arrive pas si forme normale *)
      | Lt =>
	let m := double_modn1 w_zdigits w_0 w_head0 w_add_mul_div w_div21
                   w_compare w_sub 1 (WW ah al) bl in
        WW w_0 (w_gcd_gt bl m)
      | Gt => W0 (* absurde *)
      end
    | Lt =>
      let m := ww_mod_gt_aux ah al bh bl in
      match m with
      | W0 => WW bh bl
      | WW mh ml =>
        match w_compare w_0 mh with
        | Eq =>
          match w_compare w_0 ml with
          | Eq => WW bh bl
          | _  =>
            let r := double_modn1 w_zdigits w_0 w_head0 w_add_mul_div w_div21
                      w_compare w_sub 1 (WW bh bl) ml in
            WW w_0 (w_gcd_gt ml r)
          end
        | Lt =>
          let r := ww_mod_gt_aux bh bl mh ml in
          match r with
          | W0 => m
          | WW rh rl => cont mh ml rh rl
          end
        | Gt => W0 (* absurde *)
        end
      end
    | Gt => W0 (* absurde *)
    end.

  Fixpoint ww_gcd_gt_aux
     (p:positive) (cont: w -> w -> w -> w -> zn2z w) (ah al bh bl : w)
        {struct p} : zn2z w :=
    ww_gcd_gt_body
       (fun mh ml rh rl => match p with
        | xH => cont mh ml rh rl
        | xO p => ww_gcd_gt_aux p (ww_gcd_gt_aux p cont) mh ml rh rl
        | xI p => ww_gcd_gt_aux p (ww_gcd_gt_aux p cont) mh ml rh rl
        end) ah al bh bl.


  (* Proof *)

  Variable w_to_Z : w -> Z.
  Notation wB  := (base w_digits).
  Notation wwB := (base (ww_digits w_digits)).
  Notation "[| x |]" := (w_to_Z x)  (at level 0, x at level 99).
  Notation "[-| c |]" :=
   (interp_carry (-1) wB w_to_Z c) (at level 0, c at level 99).

  Notation "[[ x ]]" := (ww_to_Z w_digits w_to_Z x)(at level 0, x at level 99).

  Variable spec_w_0   : [|w_0|] = 0.
  Variable spec_to_Z  : forall x, 0 <= [|x|] < wB.
  Variable spec_to_w_Z  : forall x, 0 <= [[x]] < wwB.

  Variable spec_w_WW : forall h l, [[w_WW h l]] = [|h|] * wB + [|l|].
  Variable spec_w_0W : forall l, [[w_0W l]] = [|l|].
  Variable spec_compare :
     forall x y, w_compare x y = Z.compare [|x|] [|y|].
  Variable spec_eq0 : forall x, w_eq0 x = true -> [|x|] = 0.

  Variable spec_opp_c : forall x, [-|w_opp_c x|] = -[|x|].
  Variable spec_opp : forall x, [|w_opp x|] = (-[|x|]) mod wB.
  Variable spec_opp_carry : forall x, [|w_opp_carry x|] = wB - [|x|] - 1.

  Variable spec_sub_c : forall x y, [-|w_sub_c x y|] = [|x|] - [|y|].
  Variable spec_sub : forall x y, [|w_sub x y|] = ([|x|] - [|y|]) mod wB.
  Variable spec_sub_carry :
	 forall x y, [|w_sub_carry x y|] = ([|x|] - [|y|] - 1) mod wB.

  Variable spec_div_gt : forall a b, [|a|] > [|b|] -> 0 < [|b|] ->
      let (q,r) := w_div_gt a b in
      [|a|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|].
  Variable spec_mod_gt : forall a b, [|a|] > [|b|] -> 0 < [|b|] ->
      [|w_mod_gt a b|] = [|a|] mod [|b|].
  Variable spec_gcd_gt : forall a b, [|a|] > [|b|] ->
      Zis_gcd [|a|] [|b|] [|w_gcd_gt a b|].

  Variable spec_add_mul_div : forall x y p,
       [|p|] <= Zpos w_digits ->
       [| w_add_mul_div p x y |] =
         ([|x|] * (2 ^ ([|p|])) +
          [|y|] / (2 ^ ((Zpos w_digits) - [|p|]))) mod wB.
  Variable spec_head0  : forall x,  0 < [|x|] ->
	 wB/ 2 <= 2 ^ [|w_head0 x|] * [|x|] < wB.

  Variable spec_div21 : forall a1 a2 b,
      wB/2 <= [|b|] ->
      [|a1|] < [|b|] ->
      let (q,r) := w_div21 a1 a2 b in
      [|a1|] *wB+ [|a2|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|].

  Variable spec_w_div32 : forall a1 a2 a3 b1 b2,
     wB/2 <= [|b1|] ->
     [[WW a1 a2]] < [[WW b1 b2]] ->
     let (q,r) := w_div32 a1 a2 a3 b1 b2 in
     [|a1|] * wwB + [|a2|] * wB  + [|a3|] =
        [|q|] *  ([|b1|] * wB + [|b2|])  + [[r]] /\
     0 <= [[r]] < [|b1|] * wB + [|b2|].

  Variable spec_w_zdigits: [|w_zdigits|] = Zpos w_digits.

  Variable spec_ww_digits_ : [[_ww_zdigits]] = Zpos (xO w_digits).
  Variable spec_ww_1 : [[ww_1]] = 1.
  Variable spec_ww_add_mul_div : forall x y p,
       [[p]] <= Zpos (xO w_digits) ->
       [[ ww_add_mul_div p x y ]] =
         ([[x]] * (2^[[p]]) +
          [[y]] / (2^(Zpos (xO w_digits) - [[p]]))) mod wwB.

  Ltac Spec_w_to_Z x :=
   let H:= fresh "HH" in
   assert (H:= spec_to_Z x).

  Ltac Spec_ww_to_Z x :=
   let H:= fresh "HH" in
   assert (H:= spec_ww_to_Z w_digits w_to_Z spec_to_Z x).

  Lemma to_Z_div_minus_p : forall x p,
   0 < [|p|] < Zpos w_digits  ->
   0 <= [|x|] / 2 ^ (Zpos w_digits - [|p|]) < 2 ^ [|p|].
  Proof.
   intros x p H;Spec_w_to_Z x.
   split. apply Zdiv_le_lower_bound;zarith.
   apply Zdiv_lt_upper_bound;zarith.
   rewrite <- Zpower_exp;zarith.
   ring_simplify ([|p|] + (Zpos w_digits - [|p|])); unfold base in HH;zarith.
  Qed.
  Hint Resolve to_Z_div_minus_p : zarith.

  Lemma spec_ww_div_gt_aux : forall ah al bh bl,
      [[WW ah al]] > [[WW bh bl]] ->
      0 < [|bh|] ->
      let (q,r) := ww_div_gt_aux ah al bh bl in
      [[WW ah al]] = [[q]] * [[WW bh bl]] + [[r]] /\
      0 <= [[r]] < [[WW bh bl]].
  Proof.
   intros ah al bh bl Hgt Hpos;unfold ww_div_gt_aux.
   change
   (let (q, r) := let p := w_head0 bh in
    match w_compare p w_0 with
    | Gt =>
      let b1 := w_add_mul_div p bh bl in
      let b2 := w_add_mul_div p bl w_0 in
      let a1 := w_add_mul_div p w_0 ah in
      let a2 := w_add_mul_div p ah al in
      let a3 := w_add_mul_div p al w_0 in
      let (q,r) := w_div32 a1 a2 a3 b1 b2 in
      (WW w_0 q, ww_add_mul_div
        (ww_sub w_0 w_WW w_opp_c w_opp_carry w_sub_c
            w_opp w_sub w_sub_carry _ww_zdigits (w_0W p)) W0 r)
    | _ => (ww_1, ww_sub w_0 w_WW w_opp_c w_opp_carry w_sub_c
            w_opp w_sub w_sub_carry (WW ah al) (WW bh bl))
    end in [[WW ah al]]=[[q]]*[[WW bh bl]]+[[r]] /\ 0 <=[[r]]< [[WW bh bl]]).
   assert (Hh := spec_head0 Hpos).
   lazy zeta.
   rewrite spec_compare; case Z.compare_spec;
    rewrite spec_w_0; intros HH.
   generalize Hh; rewrite HH; simpl Z.pow;
        rewrite Z.mul_1_l; intros (HH1, HH2); clear HH.
   assert (wwB <= 2*[[WW bh bl]]).
    apply Z.le_trans with (2*[|bh|]*wB).
    rewrite wwB_wBwB; rewrite Z.pow_2_r; apply Z.mul_le_mono_nonneg_r; zarith.
    rewrite <- wB_div_2; apply Z.mul_le_mono_nonneg_l; zarith.
    simpl ww_to_Z;rewrite Z.mul_add_distr_l;rewrite Z.mul_assoc.
    Spec_w_to_Z bl;zarith.
   Spec_ww_to_Z (WW ah al).
   rewrite spec_ww_sub;eauto.
   simpl;rewrite spec_ww_1;rewrite Z.mul_1_l;simpl.
   simpl ww_to_Z in Hgt, H, HH;rewrite Zmod_small;split;zarith.
   case (spec_to_Z (w_head0 bh)); auto with zarith.
   assert ([|w_head0 bh|] < Zpos w_digits).
    destruct (Z_lt_ge_dec [|w_head0 bh|]  (Zpos w_digits));trivial.
    exfalso.
    assert (2 ^ [|w_head0 bh|] * [|bh|] >= wB);auto with zarith.
    apply Z.le_ge; replace wB with (wB * 1);try ring.
    Spec_w_to_Z bh;apply Z.mul_le_mono_nonneg;zarith.
    unfold base;apply Zpower_le_monotone;zarith.
   assert (HHHH : 0 < [|w_head0 bh|] < Zpos w_digits); auto with zarith.
   assert (Hb:= Z.lt_le_incl _ _ H).
   generalize (spec_add_mul_div w_0 ah Hb)
    (spec_add_mul_div ah al Hb)
    (spec_add_mul_div al w_0 Hb)
    (spec_add_mul_div bh bl Hb)
    (spec_add_mul_div bl w_0  Hb);
   rewrite spec_w_0; repeat rewrite Z.mul_0_l;repeat rewrite Z.add_0_l;
   rewrite Zdiv_0_l;repeat rewrite Z.add_0_r.
   Spec_w_to_Z ah;Spec_w_to_Z bh.
   unfold base;repeat rewrite Zmod_shift_r;zarith.
   assert (H3:=to_Z_div_minus_p ah HHHH);assert(H4:=to_Z_div_minus_p al HHHH);
   assert (H5:=to_Z_div_minus_p bl HHHH).
   rewrite Z.mul_comm in Hh.
   assert (2^[|w_head0 bh|] < wB). unfold base;apply Zpower_lt_monotone;zarith.
   unfold base in H0;rewrite Zmod_small;zarith.
   fold wB; rewrite (Zmod_small ([|bh|] * 2 ^ [|w_head0 bh|]));zarith.
   intros U1 U2 U3 V1 V2.
   generalize (@spec_w_div32 (w_add_mul_div (w_head0 bh) w_0 ah)
               (w_add_mul_div (w_head0 bh) ah al)
               (w_add_mul_div (w_head0 bh) al w_0)
               (w_add_mul_div (w_head0 bh) bh bl)
               (w_add_mul_div (w_head0 bh) bl w_0)).
   destruct (w_div32 (w_add_mul_div (w_head0 bh) w_0 ah)
              (w_add_mul_div (w_head0 bh) ah al)
              (w_add_mul_div (w_head0 bh) al w_0)
              (w_add_mul_div (w_head0 bh) bh bl)
              (w_add_mul_div (w_head0 bh) bl w_0)) as (q,r).
   rewrite V1;rewrite V2. rewrite Z.mul_add_distr_r.
   rewrite <- (Z.add_assoc ([|bh|] * 2 ^ [|w_head0 bh|] * wB)).
   unfold base;rewrite <- shift_unshift_mod;zarith. fold wB.
   replace ([|bh|] * 2 ^ [|w_head0 bh|] * wB + [|bl|] * 2 ^ [|w_head0 bh|]) with
    ([[WW bh bl]] * 2^[|w_head0 bh|]). 2:simpl;ring.
   fold wwB. rewrite wwB_wBwB. rewrite Z.pow_2_r. rewrite U1;rewrite U2;rewrite U3.
   rewrite Z.mul_assoc. rewrite Z.mul_add_distr_r.
   rewrite (Z.add_assoc ([|ah|] / 2^(Zpos(w_digits) - [|w_head0 bh|])*wB * wB)).
   rewrite <- Z.mul_add_distr_r.  rewrite <- Z.add_assoc.
   unfold base;repeat rewrite <- shift_unshift_mod;zarith. fold wB.
   replace ([|ah|] * 2 ^ [|w_head0 bh|] * wB + [|al|] * 2 ^ [|w_head0 bh|]) with
    ([[WW ah al]] * 2^[|w_head0 bh|]). 2:simpl;ring.
   intros Hd;destruct Hd;zarith.
   simpl. apply beta_lex_inv;zarith. rewrite U1;rewrite V1.
   assert ([|ah|] / 2 ^ (Zpos (w_digits) - [|w_head0 bh|]) < wB/2);zarith.
   apply Zdiv_lt_upper_bound;zarith.
   unfold base.
   replace (2^Zpos (w_digits)) with (2^(Zpos (w_digits) - 1)*2).
   rewrite Z_div_mult;zarith.  rewrite <- Zpower_exp;zarith.
   apply Z.lt_le_trans with wB;zarith.
   unfold base;apply Zpower_le_monotone;zarith.
   pattern 2 at 2;replace 2 with (2^1);trivial.
   rewrite <- Zpower_exp;zarith. ring_simplify (Zpos (w_digits) - 1 + 1);trivial.
   change [[WW w_0 q]] with ([|w_0|]*wB+[|q|]);rewrite spec_w_0;rewrite
   Z.mul_0_l;rewrite Z.add_0_l.
   replace [[ww_add_mul_div (ww_sub w_0 w_WW w_opp_c w_opp_carry w_sub_c w_opp w_sub w_sub_carry
       _ww_zdigits (w_0W (w_head0 bh))) W0 r]] with ([[r]]/2^[|w_head0 bh|]).
   assert (0 < 2^[|w_head0 bh|]). apply Z.pow_pos_nonneg;zarith.
   split.
   rewrite <- (Z_div_mult [[WW ah al]] (2^[|w_head0 bh|]));zarith.
   rewrite H1;rewrite Z.mul_assoc;apply Z_div_plus_l;trivial.
   split;[apply Zdiv_le_lower_bound| apply Zdiv_lt_upper_bound];zarith.
   rewrite spec_ww_add_mul_div.
   rewrite spec_ww_sub; auto with zarith.
   rewrite spec_ww_digits_.
   change (Zpos (xO (w_digits))) with (2*Zpos (w_digits));zarith.
   simpl ww_to_Z;rewrite Z.mul_0_l;rewrite Z.add_0_l.
   rewrite spec_w_0W.
   rewrite (fun x y => Zmod_small (x-y)); auto with zarith.
   ring_simplify (2 * Zpos w_digits - (2 * Zpos w_digits - [|w_head0 bh|])).
   rewrite Zmod_small;zarith.
   split;[apply Zdiv_le_lower_bound| apply Zdiv_lt_upper_bound];zarith.
   Spec_ww_to_Z r.
   apply Z.lt_le_trans with wwB;zarith.
   rewrite <- (Z.mul_1_r wwB);apply Z.mul_le_mono_nonneg;zarith.
   split; auto with zarith.
   apply Z.le_lt_trans with (2 * Zpos w_digits); auto with zarith.
   unfold base, ww_digits; rewrite (Pos2Z.inj_xO w_digits).
   apply Zpower2_lt_lin; auto with zarith.
   rewrite spec_ww_sub; auto with zarith.
   rewrite spec_ww_digits_; rewrite spec_w_0W.
   rewrite Zmod_small;zarith.
   rewrite Pos2Z.inj_xO; split; auto with zarith.
   apply Z.le_lt_trans with (2 * Zpos w_digits); auto with zarith.
   unfold base, ww_digits; rewrite (Pos2Z.inj_xO w_digits).
   apply Zpower2_lt_lin; auto with zarith.
   Qed.

  Lemma spec_ww_div_gt : forall a b, [[a]] > [[b]] -> 0 < [[b]] ->
      let (q,r) := ww_div_gt a b in
      [[a]] = [[q]] * [[b]] + [[r]] /\
      0 <= [[r]] < [[b]].
  Proof.
   intros a b Hgt Hpos;unfold ww_div_gt.
   change (let (q,r) :=   match a, b with
  | W0, _ => (W0,W0)
  | _, W0 => (W0,W0)
  | WW ah al, WW bh bl =>
    if w_eq0 ah then
     let (q,r) := w_div_gt al bl in
     (WW w_0 q, w_0W r)
    else
     match w_compare w_0 bh with
     | Eq =>
       let(q,r):=
        double_divn1 w_zdigits w_0 w_WW w_head0 w_add_mul_div w_div21
                  w_compare w_sub 1 a bl in
       (q, w_0W r)
     | Lt => ww_div_gt_aux ah al bh bl
     | Gt => (W0,W0) (* cas absurde *)
     end
  end in [[a]] = [[q]] * [[b]] + [[r]] /\ 0 <= [[r]] < [[b]]).
   destruct a as [ |ah al]. simpl in Hgt;omega.
   destruct b as [ |bh bl]. simpl in Hpos;omega.
   Spec_w_to_Z ah; Spec_w_to_Z al; Spec_w_to_Z bh; Spec_w_to_Z bl.
   assert (H:=@spec_eq0 ah);destruct (w_eq0 ah).
   simpl ww_to_Z;rewrite H;trivial. simpl in Hgt;rewrite H in Hgt;trivial.
   assert ([|bh|] <= 0).
   apply beta_lex with (d:=[|al|])(b:=[|bl|]) (beta := wB);zarith.
   assert ([|bh|] = 0);zarith. rewrite H1 in Hgt;rewrite H1;simpl in Hgt.
   simpl. simpl in Hpos;rewrite H1 in Hpos;simpl in Hpos.
   assert (H2:=spec_div_gt Hgt Hpos);destruct (w_div_gt al bl).
   repeat rewrite spec_w_0W;simpl;rewrite spec_w_0;simpl;trivial.
   clear H.
   rewrite spec_compare; case Z.compare_spec; intros Hcmp.
   rewrite spec_w_0 in Hcmp. change [[WW bh bl]] with ([|bh|]*wB+[|bl|]).
   rewrite <- Hcmp;rewrite Z.mul_0_l;rewrite Z.add_0_l.
   simpl in Hpos;rewrite <- Hcmp in Hpos;simpl in Hpos.
   assert (H2:= @spec_double_divn1 w w_digits w_zdigits w_0 w_WW w_head0 w_add_mul_div
    w_div21 w_compare w_sub w_to_Z spec_to_Z spec_w_zdigits spec_w_0 spec_w_WW spec_head0
    spec_add_mul_div spec_div21 spec_compare spec_sub 1 (WW ah al) bl Hpos).
   destruct (double_divn1 w_zdigits w_0 w_WW w_head0 w_add_mul_div w_div21
              w_compare w_sub 1
             (WW ah al) bl).
   rewrite spec_w_0W;unfold ww_to_Z;trivial.
   apply spec_ww_div_gt_aux;trivial. rewrite spec_w_0 in Hcmp;trivial.
   rewrite spec_w_0 in Hcmp;exfalso;omega.
  Qed.

  Lemma spec_ww_mod_gt_aux_eq : forall ah al bh bl,
   ww_mod_gt_aux ah al bh bl = snd (ww_div_gt_aux ah al bh bl).
  Proof.
   intros ah al bh bl. unfold ww_mod_gt_aux, ww_div_gt_aux.
   case w_compare; auto.
   case w_div32; auto.
  Qed.

  Lemma spec_ww_mod_gt_aux : forall ah al bh bl,
   [[WW ah al]] > [[WW bh bl]] ->
    0 < [|bh|] ->
    [[ww_mod_gt_aux ah al bh bl]] = [[WW ah al]] mod [[WW bh bl]].
  Proof.
   intros. rewrite spec_ww_mod_gt_aux_eq;trivial.
   assert (H3 := spec_ww_div_gt_aux ah al bl H H0).
   destruct (ww_div_gt_aux ah al bh bl) as (q,r);simpl. simpl in H,H3.
   destruct H3;apply Zmod_unique with [[q]];zarith.
   rewrite H1;ring.
  Qed.

  Lemma spec_w_mod_gt_eq : forall a b, [|a|] > [|b|] -> 0 <[|b|] ->
    [|w_mod_gt a b|] = [|snd (w_div_gt a b)|].
  Proof.
   intros a b Hgt Hpos.
   rewrite spec_mod_gt;trivial.
   assert (H:=spec_div_gt Hgt Hpos).
   destruct (w_div_gt a b) as (q,r);simpl.
   rewrite Z.mul_comm in H;destruct H.
   symmetry;apply Zmod_unique with [|q|];trivial.
  Qed.

  Lemma spec_ww_mod_gt_eq : forall a b, [[a]] > [[b]] -> 0 < [[b]] ->
      [[ww_mod_gt a b]] = [[snd (ww_div_gt a b)]].
  Proof.
   intros a b Hgt Hpos.
   change (ww_mod_gt a b) with
   (match a, b with
  | W0, _ => W0
  | _, W0 => W0
  | WW ah al, WW bh bl =>
    if w_eq0 ah then w_0W (w_mod_gt al bl)
    else
     match w_compare w_0 bh with
     | Eq =>
       w_0W (double_modn1 w_zdigits w_0 w_head0 w_add_mul_div w_div21
             w_compare w_sub 1 a bl)
     | Lt => ww_mod_gt_aux ah al bh bl
     | Gt => W0 (* cas absurde *)
     end end).
   change (ww_div_gt a b) with
   (match a, b with
  | W0, _ => (W0,W0)
  | _, W0 => (W0,W0)
  | WW ah al, WW bh bl =>
    if w_eq0 ah then
     let (q,r) := w_div_gt al bl in
     (WW w_0 q, w_0W r)
    else
     match w_compare w_0 bh with
     | Eq =>
       let(q,r):=
        double_divn1 w_zdigits w_0 w_WW w_head0 w_add_mul_div w_div21
                  w_compare w_sub 1 a bl in
       (q, w_0W r)
     | Lt => ww_div_gt_aux ah al bh bl
     | Gt => (W0,W0) (* cas absurde *)
     end
  end).
   destruct a as [ |ah al];trivial.
   destruct b as [ |bh bl];trivial.
   Spec_w_to_Z ah; Spec_w_to_Z al; Spec_w_to_Z bh; Spec_w_to_Z bl.
   assert (H:=@spec_eq0 ah);destruct (w_eq0 ah).
   simpl in Hgt;rewrite H in Hgt;trivial.
   assert ([|bh|] <= 0).
   apply beta_lex with (d:=[|al|])(b:=[|bl|]) (beta := wB);zarith.
   assert ([|bh|] = 0);zarith. rewrite H1 in Hgt;simpl in Hgt.
   simpl in Hpos;rewrite H1 in Hpos;simpl in Hpos.
   rewrite spec_w_0W;rewrite spec_w_mod_gt_eq;trivial.
   destruct (w_div_gt al bl);simpl;rewrite spec_w_0W;trivial.
   clear H.
   rewrite spec_compare; case Z.compare_spec; intros H2.
   rewrite (@spec_double_modn1_aux w w_zdigits w_0 w_WW w_head0 w_add_mul_div
            w_div21 w_compare w_sub w_to_Z spec_w_0 spec_compare 1 (WW ah al) bl).
   destruct (double_divn1 w_zdigits w_0 w_WW w_head0 w_add_mul_div w_div21 w_compare w_sub 1
             (WW ah al) bl);simpl;trivial.
   rewrite spec_ww_mod_gt_aux_eq;trivial;symmetry;trivial.
   trivial.
  Qed.

  Lemma spec_ww_mod_gt : forall a b, [[a]] > [[b]] -> 0 < [[b]] ->
      [[ww_mod_gt a b]] = [[a]] mod [[b]].
  Proof.
   intros a b Hgt Hpos.
   assert (H:= spec_ww_div_gt a b Hgt Hpos).
   rewrite (spec_ww_mod_gt_eq a b Hgt Hpos).
   destruct (ww_div_gt a b)as(q,r);destruct H.
   apply Zmod_unique with[[q]];simpl;trivial.
   rewrite Z.mul_comm;trivial.
  Qed.

  Lemma Zis_gcd_mod : forall a b d,
   0 < b -> Zis_gcd b (a mod b) d -> Zis_gcd a b d.
  Proof.
   intros a b d H H1; apply Zis_gcd_for_euclid with (a/b).
   pattern a at 1;rewrite (Z_div_mod_eq a b).
   ring_simplify (b * (a / b) + a mod b - a / b * b);trivial. zarith.
  Qed.

  Lemma spec_ww_gcd_gt_aux_body :
   forall ah al bh bl n cont,
    [[WW bh bl]] <= 2^n ->
    [[WW ah al]] > [[WW bh bl]] ->
    (forall xh xl yh yl,
     [[WW xh xl]] > [[WW yh yl]] -> [[WW yh yl]] <= 2^(n-1) ->
     Zis_gcd [[WW xh xl]] [[WW yh yl]] [[cont xh xl yh yl]]) ->
    Zis_gcd [[WW ah al]] [[WW bh bl]] [[ww_gcd_gt_body cont ah al bh bl]].
  Proof.
   intros ah al bh bl n cont Hlog Hgt Hcont.
   change (ww_gcd_gt_body cont ah al bh bl) with (match w_compare w_0 bh with
    | Eq =>
      match w_compare w_0 bl with
      | Eq => WW ah al (* normalement n'arrive pas si forme normale *)
      | Lt =>
	let m := double_modn1 w_zdigits w_0 w_head0 w_add_mul_div w_div21
                   w_compare w_sub 1 (WW ah al) bl in
        WW w_0 (w_gcd_gt bl m)
      | Gt => W0 (* absurde *)
      end
    | Lt =>
      let m := ww_mod_gt_aux ah al bh bl in
      match m with
      | W0 => WW bh bl
      | WW mh ml =>
        match w_compare w_0 mh with
        | Eq =>
          match w_compare w_0 ml with
          | Eq => WW bh bl
          | _  =>
            let r := double_modn1 w_zdigits w_0 w_head0 w_add_mul_div w_div21
                      w_compare w_sub 1 (WW bh bl) ml in
            WW w_0 (w_gcd_gt ml r)
          end
        | Lt =>
          let r := ww_mod_gt_aux bh bl mh ml in
          match r with
          | W0 => m
          | WW rh rl => cont mh ml rh rl
          end
        | Gt => W0 (* absurde *)
        end
      end
    | Gt => W0 (* absurde *)
    end).
   rewrite spec_compare, spec_w_0.
   case Z.compare_spec; intros Hbh.
   simpl ww_to_Z in *. rewrite <- Hbh.
   rewrite Z.mul_0_l;rewrite Z.add_0_l.
   rewrite spec_compare, spec_w_0.
   case Z.compare_spec; intros Hbl.
   rewrite <- Hbl;apply Zis_gcd_0.
   simpl;rewrite spec_w_0;rewrite Z.mul_0_l;rewrite Z.add_0_l.
   apply Zis_gcd_mod;zarith.
   change ([|ah|] * wB + [|al|]) with (double_to_Z w_digits w_to_Z 1 (WW ah al)).
   rewrite <- (@spec_double_modn1 w w_digits w_zdigits w_0 w_WW w_head0 w_add_mul_div
    w_div21 w_compare w_sub w_to_Z spec_to_Z spec_w_zdigits spec_w_0 spec_w_WW spec_head0 spec_add_mul_div
    spec_div21 spec_compare spec_sub 1 (WW ah al) bl Hbl).
   apply spec_gcd_gt.
   rewrite  (@spec_double_modn1 w w_digits w_zdigits w_0 w_WW); trivial.
   apply Z.lt_gt;match goal with | |- ?x mod ?y < ?y =>
    destruct (Z_mod_lt x y);zarith end.
   Spec_w_to_Z bl;exfalso;omega.
   assert (H:= spec_ww_mod_gt_aux _ _ _ Hgt Hbh).
   assert (H2 : 0 < [[WW bh bl]]).
   simpl;Spec_w_to_Z bl. apply Z.lt_le_trans with ([|bh|]*wB);zarith.
   apply Z.mul_pos_pos;zarith.
   apply Zis_gcd_mod;trivial. rewrite <- H.
   simpl in *;destruct (ww_mod_gt_aux ah al bh bl) as [ |mh ml].
   simpl;apply Zis_gcd_0;zarith.
   rewrite spec_compare, spec_w_0; case Z.compare_spec; intros Hmh.
   simpl;rewrite <- Hmh;simpl.
   rewrite spec_compare, spec_w_0; case Z.compare_spec; intros Hml.
   rewrite <- Hml;simpl;apply Zis_gcd_0.
   simpl; rewrite spec_w_0; simpl.
   apply Zis_gcd_mod;zarith.
   change ([|bh|] * wB + [|bl|]) with (double_to_Z w_digits w_to_Z 1 (WW bh bl)).
   rewrite <- (@spec_double_modn1 w w_digits w_zdigits w_0 w_WW w_head0 w_add_mul_div
   w_div21 w_compare w_sub w_to_Z spec_to_Z spec_w_zdigits spec_w_0 spec_w_WW spec_head0 spec_add_mul_div
   spec_div21 spec_compare spec_sub 1 (WW bh bl) ml Hml).
   apply spec_gcd_gt.
   rewrite  (@spec_double_modn1 w w_digits w_zdigits w_0 w_WW); trivial.
   apply Z.lt_gt;match goal with | |- ?x mod ?y < ?y =>
   destruct (Z_mod_lt x y);zarith end.
   Spec_w_to_Z ml;exfalso;omega.
   assert ([[WW bh bl]] > [[WW mh ml]]).
   rewrite H;simpl; apply Z.lt_gt;match goal with | |- ?x mod ?y < ?y =>
   destruct (Z_mod_lt x y);zarith end.
   assert (H1:= spec_ww_mod_gt_aux _ _ _ H0 Hmh).
   assert (H3 : 0 < [[WW mh ml]]).
   simpl;Spec_w_to_Z ml. apply Z.lt_le_trans with ([|mh|]*wB);zarith.
   apply Z.mul_pos_pos;zarith.
   apply Zis_gcd_mod;zarith. simpl in *;rewrite <- H1.
   destruct (ww_mod_gt_aux bh bl mh ml) as [ |rh rl]. simpl; apply Zis_gcd_0.
   simpl;apply Hcont. simpl in H1;rewrite H1.
   apply Z.lt_gt;match goal with | |- ?x mod ?y < ?y =>
   destruct (Z_mod_lt x y);zarith end.
   apply Z.le_trans with (2^n/2).
   apply Zdiv_le_lower_bound;zarith.
   apply Z.le_trans with ([|bh|] * wB + [|bl|]);zarith.
   assert (H3' := Z_div_mod_eq [[WW bh bl]] [[WW mh ml]] (Z.lt_gt _ _ H3)).
   assert (H4 : 0 <= [[WW bh bl]]/[[WW mh ml]]).
   apply Z.ge_le;apply Z_div_ge0;zarith. simpl in *;rewrite H1.
   pattern ([|bh|] * wB + [|bl|]) at 2;rewrite H3'.
   Z.le_elim H4.
   assert (H6' : [[WW bh bl]] mod [[WW mh ml]] =
                  [[WW bh bl]] - [[WW mh ml]] * ([[WW bh bl]]/[[WW mh ml]])).
   simpl;pattern ([|bh|] * wB + [|bl|]) at 2;rewrite H3';ring. simpl in H6'.
   assert ([[WW mh ml]] <= [[WW mh ml]] * ([[WW bh bl]]/[[WW mh ml]])).
   simpl;pattern ([|mh|]*wB+[|ml|]) at 1;rewrite <- Z.mul_1_r;zarith.
   simpl in *;assert (H8 := Z_mod_lt [[WW bh bl]] [[WW mh ml]]);simpl in H8;
    zarith.
   assert (H8 := Z_mod_lt [[WW bh bl]] [[WW mh ml]]);simpl in *;zarith.
   rewrite <- H4 in H3';rewrite Z.mul_0_r in H3';simpl in H3';zarith.
   pattern n at 1;replace n with (n-1+1);try ring.
   rewrite Zpower_exp;zarith. change (2^1) with 2.
   rewrite Z_div_mult;zarith.
   assert (2^1 <= 2^n). change (2^1) with 2;zarith.
   assert (H7 := @Zpower_le_monotone_inv 2 1 n);zarith.
   Spec_w_to_Z mh;exfalso;zarith.
   Spec_w_to_Z bh;exfalso;zarith.
  Qed.

  Lemma spec_ww_gcd_gt_aux :
   forall p cont n,
   (forall xh xl yh yl,
     [[WW xh xl]] > [[WW yh yl]] ->
     [[WW yh yl]] <= 2^n ->
      Zis_gcd [[WW xh xl]] [[WW yh yl]] [[cont xh xl yh yl]]) ->
   forall ah al bh bl , [[WW ah al]] > [[WW bh bl]] ->
     [[WW bh bl]] <= 2^(Zpos p + n) ->
     Zis_gcd [[WW ah al]] [[WW bh bl]]
        [[ww_gcd_gt_aux p cont ah al bh bl]].
  Proof.
   induction p;intros cont n Hcont ah al bh bl Hgt Hs;simpl ww_gcd_gt_aux.
   assert (0 < Zpos p). unfold Z.lt;reflexivity.
   apply spec_ww_gcd_gt_aux_body with (n := Zpos (xI p) + n);
   trivial;rewrite Pos2Z.inj_xI.
   intros. apply IHp with (n := Zpos p + n);zarith.
   intros. apply IHp with (n := n );zarith.
   apply Z.le_trans with (2 ^ (2* Zpos p + 1+ n -1));zarith.
   apply Z.pow_le_mono_r;zarith.
   assert (0 < Zpos p). unfold Z.lt;reflexivity.
   apply spec_ww_gcd_gt_aux_body with (n := Zpos (xO p) + n );trivial.
   rewrite (Pos2Z.inj_xO p).
   intros. apply IHp with (n := Zpos p + n - 1);zarith.
   intros. apply IHp with (n := n -1 );zarith.
   intros;apply Hcont;zarith.
   apply Z.le_trans with (2^(n-1));zarith.
   apply Z.pow_le_mono_r;zarith.
   apply Z.le_trans with (2 ^ (Zpos p + n -1));zarith.
   apply Z.pow_le_mono_r;zarith.
   apply Z.le_trans with (2 ^ (2*Zpos p + n -1));zarith.
   apply Z.pow_le_mono_r;zarith.
   apply spec_ww_gcd_gt_aux_body with (n := n+1);trivial.
   rewrite Z.add_comm;trivial.
   ring_simplify (n + 1 - 1);trivial.
  Qed.

End DoubleDivGt.

Section DoubleDiv.

 Variable w : Type.
 Variable w_digits : positive.
 Variable ww_1 : zn2z w.
 Variable ww_compare : zn2z w -> zn2z w -> comparison.

 Variable ww_div_gt : zn2z w -> zn2z w -> zn2z w * zn2z w.
 Variable ww_mod_gt : zn2z w -> zn2z w -> zn2z w.

 Definition ww_div a b :=
  match ww_compare a b with
  | Gt => ww_div_gt a b
  | Eq => (ww_1, W0)
  | Lt => (W0, a)
  end.

 Definition ww_mod a b :=
  match ww_compare a b with
  | Gt => ww_mod_gt a b
  | Eq => W0
  | Lt => a
  end.

  Variable w_to_Z : w -> Z.
  Notation wB  := (base w_digits).
  Notation wwB := (base (ww_digits w_digits)).
  Notation "[| x |]" := (w_to_Z x)  (at level 0, x at level 99).
  Notation "[[ x ]]" := (ww_to_Z w_digits w_to_Z x)(at level 0, x at level 99).
  Variable spec_to_Z  : forall x, 0 <= [|x|] < wB.
  Variable spec_ww_1 : [[ww_1]] = 1.
  Variable spec_ww_compare :  forall x y,
    ww_compare x y = Z.compare [[x]] [[y]].
  Variable spec_ww_div_gt : forall a b, [[a]] > [[b]] -> 0 < [[b]] ->
      let (q,r) := ww_div_gt a b in
      [[a]] = [[q]] * [[b]] + [[r]] /\
      0 <= [[r]] < [[b]].
  Variable spec_ww_mod_gt : forall a b, [[a]] > [[b]] -> 0 < [[b]] ->
      [[ww_mod_gt a b]] = [[a]] mod [[b]].

  Ltac Spec_w_to_Z x :=
   let H:= fresh "HH" in
   assert (H:= spec_to_Z x).

  Ltac Spec_ww_to_Z x :=
   let H:= fresh "HH" in
   assert (H:= spec_ww_to_Z w_digits w_to_Z spec_to_Z x).

  Lemma spec_ww_div : forall a b, 0 < [[b]] ->
      let (q,r) := ww_div a b in
      [[a]] = [[q]] * [[b]] + [[r]] /\
      0 <= [[r]] < [[b]].
  Proof.
   intros a b Hpos;unfold ww_div.
   rewrite spec_ww_compare; case Z.compare_spec; intros.
   simpl;rewrite spec_ww_1;split;zarith.
   simpl;split;[ring|Spec_ww_to_Z a;zarith].
   apply spec_ww_div_gt;auto with zarith.
  Qed.

  Lemma  spec_ww_mod :  forall a b, 0 < [[b]] ->
      [[ww_mod a b]] = [[a]] mod [[b]].
  Proof.
   intros a b Hpos;unfold ww_mod.
   rewrite spec_ww_compare; case Z.compare_spec; intros.
   simpl;apply Zmod_unique with 1;try rewrite H;zarith.
   Spec_ww_to_Z a;symmetry;apply Zmod_small;zarith.
   apply spec_ww_mod_gt;auto with zarith.
  Qed.


 Variable w_0 : w.
 Variable w_1 : w.
 Variable w_compare : w -> w -> comparison.
 Variable w_eq0 : w -> bool.
 Variable w_gcd_gt : w -> w -> w.
 Variable _ww_digits : positive.
 Variable spec_ww_digits_ : _ww_digits = xO w_digits.
 Variable ww_gcd_gt_fix :
   positive -> (w -> w -> w -> w -> zn2z w) ->
             w -> w -> w -> w -> zn2z w.

  Variable spec_w_0   : [|w_0|] = 0.
  Variable spec_w_1   : [|w_1|] = 1.
  Variable spec_compare :
    forall x y, w_compare x y = Z.compare [|x|] [|y|].
  Variable spec_eq0 : forall x, w_eq0 x = true -> [|x|] = 0.
  Variable spec_gcd_gt : forall a b, [|a|] > [|b|] ->
      Zis_gcd [|a|] [|b|] [|w_gcd_gt a b|].
  Variable spec_gcd_gt_fix :
   forall p cont n,
   (forall xh xl yh yl,
     [[WW xh xl]] > [[WW yh yl]] ->
     [[WW yh yl]] <= 2^n ->
      Zis_gcd [[WW xh xl]] [[WW yh yl]] [[cont xh xl yh yl]]) ->
   forall ah al bh bl , [[WW ah al]] > [[WW bh bl]] ->
     [[WW bh bl]] <= 2^(Zpos p + n) ->
     Zis_gcd [[WW ah al]] [[WW bh bl]]
        [[ww_gcd_gt_fix p cont ah al bh bl]].

 Definition gcd_cont (xh xl yh yl:w) :=
  match w_compare w_1 yl with
  | Eq => ww_1
  | _ => WW xh xl
  end.

  Lemma spec_gcd_cont : forall xh xl yh yl,
     [[WW xh xl]] > [[WW yh yl]] ->
     [[WW yh yl]] <= 1 ->
      Zis_gcd [[WW xh xl]] [[WW yh yl]] [[gcd_cont xh xl yh yl]].
  Proof.
   intros xh xl yh yl Hgt' Hle. simpl in Hle.
   assert ([|yh|] = 0).
    change 1 with (0*wB+1) in Hle.
    assert (0 <= 1 < wB). split;zarith. apply wB_pos.
    assert (H1:= beta_lex _ _ _ _ _ Hle (spec_to_Z yl) H).
    Spec_w_to_Z yh;zarith.
   unfold gcd_cont; rewrite spec_compare, spec_w_1.
   case Z.compare_spec; intros Hcmpy.
   simpl;rewrite H;simpl;
   rewrite spec_ww_1;rewrite <- Hcmpy;apply Zis_gcd_mod;zarith.
   rewrite <- (Zmod_unique ([|xh|]*wB+[|xl|]) 1 ([|xh|]*wB+[|xl|]) 0);zarith.
   rewrite H in Hle; exfalso;zarith.
   assert (H0 : [|yl|] = 0) by (Spec_w_to_Z yl;zarith).
   simpl. rewrite H0, H;simpl;apply Zis_gcd_0;trivial.
  Qed.


  Variable cont : w -> w -> w -> w -> zn2z w.
  Variable spec_cont : forall xh xl yh yl,
     [[WW xh xl]] > [[WW yh yl]] ->
     [[WW yh yl]] <= 1 ->
      Zis_gcd [[WW xh xl]] [[WW yh yl]] [[cont xh xl yh yl]].

  Definition ww_gcd_gt a b :=
   match a, b with
   | W0, _ => b
   | _, W0 => a
   | WW ah al, WW bh bl =>
     if w_eq0 ah then (WW w_0 (w_gcd_gt al bl))
     else ww_gcd_gt_fix _ww_digits cont ah al bh bl
   end.

  Definition ww_gcd a b :=
   Eval lazy beta delta [ww_gcd_gt] in
   match ww_compare a b with
   | Gt => ww_gcd_gt a b
   | Eq => a
   | Lt => ww_gcd_gt b a
   end.

  Lemma spec_ww_gcd_gt : forall a b, [[a]] > [[b]] ->
      Zis_gcd [[a]] [[b]] [[ww_gcd_gt a b]].
  Proof.
   intros a b Hgt;unfold ww_gcd_gt.
   destruct a as [ |ah al]. simpl;apply Zis_gcd_sym;apply Zis_gcd_0.
   destruct b as [ |bh bl]. simpl;apply Zis_gcd_0.
   simpl in Hgt. generalize (@spec_eq0 ah);destruct (w_eq0 ah);intros.
   simpl;rewrite H in Hgt;trivial;rewrite H;trivial;rewrite spec_w_0;simpl.
   assert ([|bh|] <= 0).
   apply beta_lex with (d:=[|al|])(b:=[|bl|]) (beta := wB);zarith.
   Spec_w_to_Z bh;assert ([|bh|] = 0);zarith. rewrite H1 in Hgt;simpl in Hgt.
   rewrite H1;simpl;auto. clear H.
   apply spec_gcd_gt_fix with (n:= 0);trivial.
   rewrite Z.add_0_r;rewrite spec_ww_digits_.
   change (2 ^ Zpos (xO w_digits)) with wwB. Spec_ww_to_Z (WW bh bl);zarith.
  Qed.

  Lemma spec_ww_gcd : forall a b, Zis_gcd [[a]] [[b]] [[ww_gcd a b]].
  Proof.
   intros a b.
   change (ww_gcd a b) with
    (match ww_compare a b with
     | Gt => ww_gcd_gt a b
     | Eq => a
     | Lt => ww_gcd_gt b a
     end).
   rewrite spec_ww_compare; case Z.compare_spec; intros Hcmp.
   Spec_ww_to_Z b;rewrite Hcmp.
   apply Zis_gcd_for_euclid with 1;zarith.
   ring_simplify ([[b]] - 1 * [[b]]). apply Zis_gcd_0;zarith.
   apply Zis_gcd_sym;apply spec_ww_gcd_gt;zarith.
   apply spec_ww_gcd_gt;zarith.
  Qed.

End DoubleDiv.


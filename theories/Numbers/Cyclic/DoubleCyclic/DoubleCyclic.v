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
Require Import DoubleAdd.
Require Import DoubleSub.
Require Import DoubleMul.
Require Import DoubleSqrt.
Require Import DoubleLift.
Require Import DoubleDivn1.
Require Import DoubleDiv.
Require Import CyclicAxioms.

Local Open Scope Z_scope.


Section Z_2nZ.

 Context {t : Type}{ops : ZnZ.Ops t}.

 Let w_digits      := ZnZ.digits.
 Let w_zdigits      := ZnZ.zdigits.

 Let w_to_Z        := ZnZ.to_Z.
 Let w_of_pos      := ZnZ.of_pos.
 Let w_head0       := ZnZ.head0.
 Let w_tail0       := ZnZ.tail0.

 Let w_0            := ZnZ.zero.
 Let w_1            := ZnZ.one.
 Let w_Bm1          := ZnZ.minus_one.

 Let w_compare     := ZnZ.compare.
 Let w_eq0         := ZnZ.eq0.

 Let w_opp_c       := ZnZ.opp_c.
 Let w_opp         := ZnZ.opp.
 Let w_opp_carry   := ZnZ.opp_carry.

 Let w_succ_c      := ZnZ.succ_c.
 Let w_add_c       := ZnZ.add_c.
 Let w_add_carry_c := ZnZ.add_carry_c.
 Let w_succ        := ZnZ.succ.
 Let w_add         := ZnZ.add.
 Let w_add_carry   := ZnZ.add_carry.

 Let w_pred_c      := ZnZ.pred_c.
 Let w_sub_c       := ZnZ.sub_c.
 Let w_sub_carry_c := ZnZ.sub_carry_c.
 Let w_pred        := ZnZ.pred.
 Let w_sub         := ZnZ.sub.
 Let w_sub_carry   := ZnZ.sub_carry.


 Let w_mul_c       := ZnZ.mul_c.
 Let w_mul         := ZnZ.mul.
 Let w_square_c    := ZnZ.square_c.

 Let w_div21       := ZnZ.div21.
 Let w_div_gt      := ZnZ.div_gt.
 Let w_div         := ZnZ.div.

 Let w_mod_gt      := ZnZ.modulo_gt.
 Let w_mod         := ZnZ.modulo.

 Let w_gcd_gt      := ZnZ.gcd_gt.
 Let w_gcd         := ZnZ.gcd.

 Let w_add_mul_div := ZnZ.add_mul_div.

 Let w_pos_mod := ZnZ.pos_mod.

 Let w_is_even     := ZnZ.is_even.
 Let w_sqrt2       := ZnZ.sqrt2.
 Let w_sqrt        := ZnZ.sqrt.

 Let _zn2z := zn2z t.

 Let wB := base w_digits.

 Let w_Bm2 := w_pred w_Bm1.

 Let ww_1 := ww_1 w_0 w_1.
 Let ww_Bm1 := ww_Bm1 w_Bm1.

 Let w_add2 a b := match w_add_c a b with C0 p => WW w_0 p | C1 p => WW w_1 p end.

 Let _ww_digits := xO w_digits.

 Let _ww_zdigits := w_add2 w_zdigits w_zdigits.

 Let to_Z := zn2z_to_Z wB w_to_Z.

 Let w_W0 := ZnZ.WO.
 Let w_0W := ZnZ.OW.
 Let w_WW := ZnZ.WW.

 Let ww_of_pos p :=
  match w_of_pos p with
  | (N0, l) => (N0, WW w_0 l)
  | (Npos ph,l) =>
    let (n,h) := w_of_pos ph in (n, w_WW h l)
  end.

 Let head0 :=
  Eval lazy beta delta [ww_head0] in
  ww_head0 w_0 w_0W w_compare w_head0 w_add2 w_zdigits _ww_zdigits.

 Let tail0 :=
  Eval lazy beta delta [ww_tail0] in
  ww_tail0 w_0 w_0W w_compare w_tail0 w_add2 w_zdigits _ww_zdigits.

 Let ww_WW := Eval lazy beta delta [ww_WW] in (@ww_WW t).
 Let ww_0W := Eval lazy beta delta [ww_0W] in (@ww_0W t).
 Let ww_W0 := Eval lazy beta delta [ww_W0] in (@ww_W0 t).

 (* ** Comparison ** *)
 Let compare :=
  Eval lazy beta delta[ww_compare] in ww_compare w_0 w_compare.

 Let eq0 (x:zn2z t) :=
  match x with
  | W0 => true
  | _ => false
  end.

 (* ** Opposites ** *)
 Let opp_c :=
  Eval lazy beta delta [ww_opp_c] in ww_opp_c w_0 w_opp_c w_opp_carry.

 Let opp :=
  Eval lazy beta delta [ww_opp] in ww_opp w_0 w_opp_c w_opp_carry w_opp.

 Let opp_carry :=
  Eval lazy beta delta [ww_opp_carry] in ww_opp_carry w_WW ww_Bm1 w_opp_carry.

 (* ** Additions ** *)

 Let succ_c :=
  Eval lazy beta delta [ww_succ_c] in ww_succ_c w_0 ww_1 w_succ_c.

 Let add_c :=
  Eval lazy beta delta [ww_add_c] in ww_add_c w_WW w_add_c w_add_carry_c.

 Let add_carry_c :=
  Eval lazy beta iota delta [ww_add_carry_c ww_succ_c] in
  ww_add_carry_c w_0 w_WW ww_1 w_succ_c w_add_c w_add_carry_c.

 Let succ :=
  Eval lazy beta delta [ww_succ] in ww_succ w_W0 ww_1 w_succ_c w_succ.

 Let add :=
  Eval lazy beta delta [ww_add] in ww_add w_add_c w_add w_add_carry.

 Let add_carry :=
  Eval lazy beta iota delta [ww_add_carry ww_succ] in
  ww_add_carry w_W0 ww_1 w_succ_c w_add_carry_c w_succ w_add w_add_carry.

 (* ** Subtractions ** *)

 Let pred_c :=
  Eval lazy beta delta [ww_pred_c] in ww_pred_c w_Bm1 w_WW ww_Bm1 w_pred_c.

 Let sub_c :=
  Eval lazy beta iota delta [ww_sub_c ww_opp_c] in
  ww_sub_c w_0 w_WW w_opp_c w_opp_carry w_sub_c w_sub_carry_c.

 Let sub_carry_c :=
  Eval lazy beta iota delta [ww_sub_carry_c ww_pred_c ww_opp_carry] in
  ww_sub_carry_c w_Bm1 w_WW ww_Bm1 w_opp_carry w_pred_c w_sub_c w_sub_carry_c.

 Let pred :=
  Eval lazy beta delta [ww_pred] in ww_pred w_Bm1 w_WW ww_Bm1 w_pred_c w_pred.

 Let sub :=
  Eval lazy beta iota delta [ww_sub ww_opp] in
  ww_sub w_0 w_WW w_opp_c w_opp_carry w_sub_c w_opp w_sub w_sub_carry.

 Let sub_carry :=
  Eval lazy beta iota delta [ww_sub_carry ww_pred ww_opp_carry] in
  ww_sub_carry w_Bm1 w_WW ww_Bm1 w_opp_carry w_pred_c w_sub_carry_c w_pred
  w_sub w_sub_carry.


 (* ** Multiplication ** *)

 Let mul_c :=
  Eval lazy beta iota delta [ww_mul_c double_mul_c] in
  ww_mul_c w_0 w_1 w_WW w_W0 w_mul_c add_c add add_carry.

 Let karatsuba_c :=
  Eval lazy beta iota delta [ww_karatsuba_c double_mul_c kara_prod] in
  ww_karatsuba_c w_0 w_1 w_WW w_W0 w_compare w_add w_sub w_mul_c
    add_c add add_carry sub_c sub.

 Let mul :=
  Eval lazy beta delta [ww_mul] in
  ww_mul w_W0 w_add w_mul_c w_mul add.

 Let square_c :=
  Eval lazy beta delta [ww_square_c] in
  ww_square_c w_0 w_1 w_WW w_W0 w_mul_c w_square_c add_c add add_carry.

 (* Division operation *)

 Let div32 :=
   Eval lazy beta iota delta [w_div32] in
   w_div32 w_0 w_Bm1 w_Bm2 w_WW w_compare w_add_c w_add_carry_c
   w_add w_add_carry w_pred w_sub w_mul_c w_div21 sub_c.

 Let div21 :=
  Eval lazy beta iota delta [ww_div21] in
   ww_div21 w_0 w_0W div32 ww_1 compare sub.

 Let low (p: zn2z t) := match p with WW _ p1 => p1 | _ => w_0 end.

 Let add_mul_div :=
  Eval lazy beta delta [ww_add_mul_div] in
  ww_add_mul_div w_0 w_WW w_W0 w_0W compare w_add_mul_div sub w_zdigits low.

 Let div_gt :=
  Eval lazy beta delta [ww_div_gt] in
  ww_div_gt w_0 w_WW w_0W w_compare w_eq0 w_opp_c w_opp
  w_opp_carry w_sub_c w_sub w_sub_carry
  w_div_gt w_add_mul_div w_head0 w_div21 div32 _ww_zdigits ww_1 add_mul_div w_zdigits.

 Let div :=
  Eval lazy beta delta [ww_div] in ww_div ww_1 compare div_gt.

 Let mod_gt :=
  Eval lazy beta delta [ww_mod_gt] in
  ww_mod_gt w_0 w_WW w_0W w_compare w_eq0 w_opp_c w_opp w_opp_carry w_sub_c w_sub w_sub_carry
  w_mod_gt w_add_mul_div w_head0 w_div21 div32 _ww_zdigits add_mul_div w_zdigits.

 Let mod_ :=
  Eval lazy beta delta [ww_mod] in ww_mod compare mod_gt.

 Let pos_mod :=
  Eval lazy beta delta [ww_pos_mod] in
    ww_pos_mod w_0 w_zdigits w_WW w_pos_mod compare w_0W low sub _ww_zdigits.

 Let is_even :=
  Eval lazy beta delta [ww_is_even] in ww_is_even w_is_even.

 Let sqrt2 :=
  Eval lazy beta delta [ww_sqrt2] in
    ww_sqrt2 w_is_even w_compare w_0 w_1 w_Bm1 w_0W w_sub w_square_c
    w_div21 w_add_mul_div w_zdigits w_add_c w_sqrt2 w_pred pred_c
    pred add_c add sub_c add_mul_div.

 Let sqrt :=
  Eval lazy beta delta [ww_sqrt] in
    ww_sqrt w_is_even w_0 w_sub w_add_mul_div w_zdigits
     _ww_zdigits w_sqrt2 pred add_mul_div head0 compare low.

 Let gcd_gt_fix :=
  Eval cbv beta delta [ww_gcd_gt_aux ww_gcd_gt_body] in
  ww_gcd_gt_aux w_0 w_WW w_0W w_compare w_opp_c w_opp w_opp_carry
      w_sub_c w_sub w_sub_carry w_gcd_gt
      w_add_mul_div w_head0 w_div21 div32 _ww_zdigits add_mul_div
      w_zdigits.

 Let gcd_cont :=
  Eval lazy beta delta [gcd_cont] in gcd_cont ww_1 w_1 w_compare.

 Let gcd_gt :=
  Eval lazy beta delta [ww_gcd_gt] in
  ww_gcd_gt w_0 w_eq0 w_gcd_gt _ww_digits gcd_gt_fix gcd_cont.

 Let gcd :=
  Eval lazy beta delta [ww_gcd] in
  ww_gcd compare w_0 w_eq0 w_gcd_gt _ww_digits gcd_gt_fix gcd_cont.

 Definition lor (x y : zn2z t) :=
  match x, y with
  | W0, _ => y
  | _, W0 => x
  | WW hx lx, WW hy ly => WW (ZnZ.lor hx hy) (ZnZ.lor lx ly)
  end.

 Definition land (x y : zn2z t) :=
  match x, y with
  | W0, _ => W0
  | _, W0 => W0
  | WW hx lx, WW hy ly => WW (ZnZ.land hx hy) (ZnZ.land lx ly)
  end.

 Definition lxor (x y : zn2z t) :=
  match x, y with
  | W0, _ => y
  | _, W0 => x
  | WW hx lx, WW hy ly => WW (ZnZ.lxor hx hy) (ZnZ.lxor lx ly)
  end.

 (* ** Record of operators on 2 words *)

 Global Instance mk_zn2z_ops : ZnZ.Ops (zn2z t) | 1 :=
  ZnZ.MkOps _ww_digits _ww_zdigits
    to_Z ww_of_pos head0 tail0
    W0 ww_1 ww_Bm1
    compare eq0
    opp_c opp opp_carry
    succ_c add_c add_carry_c
    succ add add_carry
    pred_c sub_c sub_carry_c
    pred sub sub_carry
    mul_c mul square_c
    div21 div_gt div
    mod_gt mod_
    gcd_gt gcd
    add_mul_div
    pos_mod
    is_even
    sqrt2
    sqrt
    lor
    land
    lxor.

 Global Instance mk_zn2z_ops_karatsuba : ZnZ.Ops (zn2z t) | 2 :=
   ZnZ.MkOps _ww_digits _ww_zdigits
    to_Z ww_of_pos head0 tail0
    W0 ww_1 ww_Bm1
    compare eq0
    opp_c opp opp_carry
    succ_c add_c add_carry_c
    succ add add_carry
    pred_c sub_c sub_carry_c
    pred sub sub_carry
    karatsuba_c mul square_c
    div21 div_gt div
    mod_gt mod_
    gcd_gt gcd
    add_mul_div
    pos_mod
    is_even
    sqrt2
    sqrt
    lor
    land
    lxor.

 (* Proof *)
 Context {specs : ZnZ.Specs ops}.
 
 Create HintDb ZnZ.

 Hint Resolve
    ZnZ.spec_to_Z
    ZnZ.spec_of_pos
    ZnZ.spec_0
    ZnZ.spec_1
    ZnZ.spec_m1
    ZnZ.spec_compare
    ZnZ.spec_eq0
    ZnZ.spec_opp_c
    ZnZ.spec_opp
    ZnZ.spec_opp_carry
    ZnZ.spec_succ_c
    ZnZ.spec_add_c
    ZnZ.spec_add_carry_c
    ZnZ.spec_succ
    ZnZ.spec_add
    ZnZ.spec_add_carry
    ZnZ.spec_pred_c
    ZnZ.spec_sub_c
    ZnZ.spec_sub_carry_c
    ZnZ.spec_pred
    ZnZ.spec_sub
    ZnZ.spec_sub_carry
    ZnZ.spec_mul_c
    ZnZ.spec_mul
    ZnZ.spec_square_c
    ZnZ.spec_div21
    ZnZ.spec_div_gt
    ZnZ.spec_div
    ZnZ.spec_modulo_gt
    ZnZ.spec_modulo
    ZnZ.spec_gcd_gt
    ZnZ.spec_gcd
    ZnZ.spec_head0
    ZnZ.spec_tail0
    ZnZ.spec_add_mul_div
    ZnZ.spec_pos_mod
    ZnZ.spec_is_even
    ZnZ.spec_sqrt2
    ZnZ.spec_sqrt
    ZnZ.spec_WO
    ZnZ.spec_OW
    ZnZ.spec_WW : ZnZ.
 
 Ltac wwauto := unfold ww_to_Z; eauto with ZnZ.

 Let wwB := base _ww_digits.

 Notation "[| x |]" := (to_Z x)  (at level 0, x at level 99).

 Notation "[+| c |]" :=
   (interp_carry 1 wwB to_Z c)  (at level 0, c at level 99).

 Notation "[-| c |]" :=
   (interp_carry (-1) wwB to_Z c)  (at level 0, c at level 99).

 Notation "[[ x ]]" := (zn2z_to_Z wwB to_Z x)  (at level 0, x at level 99).

 Let spec_ww_to_Z   : forall x, 0 <= [| x |] < wwB.
 Proof. refine (spec_ww_to_Z w_digits w_to_Z _); wwauto. Qed.

 Let spec_ww_of_pos : forall p,
     Zpos p = (Z.of_N (fst (ww_of_pos p)))*wwB + [|(snd (ww_of_pos p))|].
 Proof.
  unfold ww_of_pos;intros.
  rewrite (ZnZ.spec_of_pos p). unfold w_of_pos.
  case (ZnZ.of_pos p); intros. simpl.
  destruct n; simpl ZnZ.to_Z.
  simpl;unfold w_to_Z,w_0; rewrite ZnZ.spec_0;trivial.
  unfold Z.of_N.
  rewrite (ZnZ.spec_of_pos p0).
  case (ZnZ.of_pos p0); intros. simpl.
  unfold fst, snd,Z.of_N, to_Z, wB, w_digits, w_to_Z, w_WW.
  rewrite ZnZ.spec_WW.
  replace wwB with (wB*wB).
  unfold wB,w_to_Z,w_digits;destruct n;ring.
  symmetry. rewrite <- Z.pow_2_r; exact (wwB_wBwB w_digits).
 Qed.

 Let spec_ww_0 : [|W0|] = 0.
 Proof. reflexivity. Qed.

 Let spec_ww_1 : [|ww_1|] = 1.
 Proof. refine (spec_ww_1 w_0 w_1 w_digits w_to_Z _ _);wwauto. Qed.

 Let spec_ww_Bm1 : [|ww_Bm1|] = wwB - 1.
 Proof. refine (spec_ww_Bm1 w_Bm1 w_digits w_to_Z _);wwauto. Qed.

 Let spec_ww_compare :
  forall x y, compare x y = Z.compare [|x|] [|y|].
 Proof.
  refine (spec_ww_compare w_0 w_digits w_to_Z w_compare _ _ _);wwauto.
 Qed.

 Let spec_ww_eq0 : forall x, eq0 x = true -> [|x|] = 0.
 Proof. destruct x;simpl;intros;trivial;discriminate. Qed.

 Let spec_ww_opp_c : forall x, [-|opp_c x|] = -[|x|].
 Proof.
  refine(spec_ww_opp_c w_0 w_0 W0 w_opp_c w_opp_carry w_digits w_to_Z _ _ _ _);
   wwauto.
 Qed.

 Let spec_ww_opp : forall x, [|opp x|] = (-[|x|]) mod wwB.
 Proof.
  refine(spec_ww_opp w_0 w_0 W0 w_opp_c w_opp_carry w_opp
   w_digits w_to_Z _ _ _ _ _);
  wwauto.
 Qed.

 Let spec_ww_opp_carry : forall x, [|opp_carry x|] = wwB - [|x|] - 1.
 Proof.
  refine (spec_ww_opp_carry w_WW ww_Bm1 w_opp_carry w_digits w_to_Z _ _ _);
  wwauto.
 Qed.

 Let spec_ww_succ_c : forall x, [+|succ_c x|] = [|x|] + 1.
 Proof.
  refine (spec_ww_succ_c w_0 w_0 ww_1 w_succ_c w_digits w_to_Z _ _ _ _);wwauto.
 Qed.

 Let spec_ww_add_c  : forall x y, [+|add_c x y|] = [|x|] + [|y|].
 Proof.
  refine (spec_ww_add_c w_WW w_add_c w_add_carry_c w_digits w_to_Z _ _ _);wwauto.
 Qed.

 Let spec_ww_add_carry_c : forall x y, [+|add_carry_c x y|] = [|x|]+[|y|]+1.
 Proof.
  refine (spec_ww_add_carry_c w_0 w_0 w_WW ww_1 w_succ_c w_add_c w_add_carry_c
   w_digits w_to_Z _ _ _ _ _ _ _);wwauto.
 Qed.

 Let spec_ww_succ : forall x, [|succ x|] = ([|x|] + 1) mod wwB.
 Proof.
  refine (spec_ww_succ w_W0 ww_1 w_succ_c w_succ w_digits w_to_Z _ _ _ _ _);
  wwauto.
 Qed.

 Let spec_ww_add : forall x y, [|add x y|] = ([|x|] + [|y|]) mod wwB.
 Proof.
  refine (spec_ww_add w_add_c w_add w_add_carry w_digits w_to_Z _ _ _ _);wwauto.
 Qed.

 Let spec_ww_add_carry : forall x y, [|add_carry x y|]=([|x|]+[|y|]+1)mod wwB.
 Proof.
  refine (spec_ww_add_carry w_W0 ww_1 w_succ_c w_add_carry_c w_succ
  w_add w_add_carry w_digits w_to_Z _ _ _ _ _ _ _ _);wwauto.
 Qed.

 Let spec_ww_pred_c : forall x, [-|pred_c x|] = [|x|] - 1.
 Proof.
  refine (spec_ww_pred_c w_0 w_Bm1 w_WW ww_Bm1 w_pred_c w_digits w_to_Z
   _ _ _ _ _);wwauto.
 Qed.

 Let spec_ww_sub_c : forall x y, [-|sub_c x y|] = [|x|] - [|y|].
 Proof.
  refine (spec_ww_sub_c w_0 w_0 w_WW W0 w_opp_c w_opp_carry w_sub_c
   w_sub_carry_c w_digits w_to_Z _ _ _ _ _ _ _);wwauto.
 Qed.

 Let spec_ww_sub_carry_c : forall x y, [-|sub_carry_c x y|] = [|x|]-[|y|]-1.
 Proof.
  refine (spec_ww_sub_carry_c w_0 w_Bm1 w_WW ww_Bm1 w_opp_carry w_pred_c
   w_sub_c w_sub_carry_c w_digits w_to_Z _ _ _ _ _ _ _ _);wwauto.
 Qed.

 Let spec_ww_pred : forall x, [|pred x|] = ([|x|] - 1) mod wwB.
 Proof.
  refine (spec_ww_pred w_0 w_Bm1 w_WW ww_Bm1 w_pred_c w_pred w_digits w_to_Z
   _ _ _ _ _ _);wwauto.
 Qed.

 Let spec_ww_sub : forall x y, [|sub x y|] = ([|x|] - [|y|]) mod wwB.
 Proof.
  refine (spec_ww_sub w_0 w_0 w_WW W0 w_opp_c w_opp_carry w_sub_c w_opp
   w_sub w_sub_carry w_digits w_to_Z _ _ _ _ _ _ _ _ _);wwauto.
 Qed.

 Let spec_ww_sub_carry : forall x y, [|sub_carry x y|]=([|x|]-[|y|]-1) mod wwB.
 Proof.
  refine (spec_ww_sub_carry w_0 w_Bm1 w_WW ww_Bm1 w_opp_carry w_pred_c
   w_sub_carry_c w_pred w_sub w_sub_carry w_digits w_to_Z _ _ _ _ _ _ _ _ _ _);
  wwauto.
 Qed.

 Let spec_ww_mul_c : forall x y, [[mul_c x y ]] = [|x|] * [|y|].
 Proof.
  refine (spec_ww_mul_c w_0 w_1 w_WW w_W0 w_mul_c add_c add add_carry w_digits
   w_to_Z _ _ _ _ _ _ _ _ _);wwauto.
 Qed.

 Let spec_ww_karatsuba_c : forall x y, [[karatsuba_c x y ]] = [|x|] * [|y|].
 Proof.
 refine (spec_ww_karatsuba_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          _ _ _ _ _ _ _ _ _ _ _ _); wwauto.
  unfold w_digits; apply ZnZ.spec_more_than_1_digit; auto.
 Qed.

 Let spec_ww_mul : forall x y, [|mul x y|] = ([|x|] * [|y|]) mod wwB.
 Proof.
  refine (spec_ww_mul w_W0 w_add w_mul_c w_mul add w_digits w_to_Z _ _ _ _ _);
  wwauto.
 Qed.

 Let spec_ww_square_c : forall x, [[square_c x]] = [|x|] * [|x|].
 Proof.
  refine (spec_ww_square_c w_0 w_1 w_WW w_W0 w_mul_c w_square_c add_c add
   add_carry w_digits w_to_Z _ _ _ _ _ _ _ _ _ _);wwauto.
 Qed.

 Let spec_w_div32 : forall a1 a2 a3 b1 b2,
       wB / 2 <= (w_to_Z b1) ->
       [|WW a1 a2|] < [|WW b1 b2|] ->
       let (q, r) := div32 a1 a2 a3 b1 b2 in
       (w_to_Z a1) * wwB + (w_to_Z a2) * wB + (w_to_Z a3) =
       (w_to_Z q) * ((w_to_Z b1)*wB + (w_to_Z b2)) + [|r|] /\
       0 <= [|r|] < (w_to_Z b1)*wB + w_to_Z b2.
 Proof.
  refine (spec_w_div32 w_0 w_Bm1 w_Bm2 w_WW w_compare w_add_c w_add_carry_c
   w_add w_add_carry w_pred w_sub w_mul_c w_div21 sub_c w_digits w_to_Z
   _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);wwauto.
  unfold w_Bm2, w_to_Z, w_pred, w_Bm1.
  rewrite ZnZ.spec_pred, ZnZ.spec_m1.
  unfold w_digits;rewrite Zmod_small. ring.
  assert (H:= wB_pos(ZnZ.digits)). omega.
  exact ZnZ.spec_div21.
 Qed.

 Let spec_ww_div21 : forall a1 a2 b,
      wwB/2 <= [|b|] ->
      [|a1|] < [|b|] ->
      let (q,r) := div21 a1 a2 b in
      [|a1|] *wwB+ [|a2|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|].
 Proof.
  refine (spec_ww_div21 w_0 w_0W div32 ww_1 compare sub w_digits w_to_Z
   _ _ _ _ _ _ _);wwauto. 
 Qed.

 Let spec_add2: forall x y,
  [|w_add2 x y|] = w_to_Z x + w_to_Z y.
  unfold w_add2.
  intros xh xl; generalize (ZnZ.spec_add_c xh xl).
  unfold w_add_c; case ZnZ.add_c; unfold interp_carry; simpl ww_to_Z.
    intros w0 Hw0; simpl; unfold w_to_Z; rewrite Hw0.
  unfold w_0; rewrite ZnZ.spec_0; simpl; auto with zarith.
  intros w0; rewrite Z.mul_1_l; simpl.
  unfold w_to_Z, w_1; rewrite ZnZ.spec_1; auto with zarith.
  rewrite Z.mul_1_l; auto.
 Qed.

 Let spec_low: forall x,
  w_to_Z (low x) = [|x|] mod wB. 
  intros x; case x; simpl low.
    unfold ww_to_Z, w_to_Z, w_0; rewrite ZnZ.spec_0; simpl; wwauto.
  intros xh xl; simpl.
  rewrite Z.add_comm; rewrite Z_mod_plus; auto with zarith.
  rewrite Zmod_small; auto with zarith.
  unfold wB, base; eauto with ZnZ zarith.
  unfold wB, base; eauto with ZnZ zarith.
 Qed.

 Let spec_ww_digits:
  [|_ww_zdigits|] = Zpos (xO w_digits).
 Proof.
 unfold w_to_Z, _ww_zdigits.
 rewrite spec_add2.
 unfold w_to_Z, w_zdigits, w_digits.
 rewrite ZnZ.spec_zdigits; auto.
 rewrite Pos2Z.inj_xO; auto with zarith.
 Qed.


 Let spec_ww_head00  : forall x,  [|x|] = 0 -> [|head0 x|] = Zpos _ww_digits.
 Proof.
 refine (spec_ww_head00 w_0 w_0W
                w_compare w_head0 w_add2 w_zdigits _ww_zdigits
                w_to_Z _ _ _ (eq_refl _ww_digits) _ _ _ _); wwauto.
 exact ZnZ.spec_head00.
 exact ZnZ.spec_zdigits.
 Qed.

 Let spec_ww_head0  : forall x,  0 < [|x|] ->
	 wwB/ 2 <= 2 ^ [|head0 x|] * [|x|] < wwB.
 Proof.
  refine (spec_ww_head0 w_0 w_0W w_compare w_head0
           w_add2 w_zdigits _ww_zdigits
   w_to_Z _ _ _ _ _ _ _);wwauto.
  exact ZnZ.spec_zdigits.
 Qed.

 Let spec_ww_tail00  : forall x,  [|x|] = 0 -> [|tail0 x|] = Zpos _ww_digits.
 Proof.
 refine (spec_ww_tail00 w_0 w_0W
                w_compare w_tail0 w_add2 w_zdigits _ww_zdigits
                w_to_Z _ _ _ (eq_refl _ww_digits) _ _ _ _); wwauto.
 exact ZnZ.spec_tail00.
 exact ZnZ.spec_zdigits.
 Qed.


 Let spec_ww_tail0  : forall x,  0 < [|x|] ->
  exists y, 0 <= y /\ [|x|] = (2 * y + 1) * 2 ^ [|tail0 x|].
 Proof.
  refine (spec_ww_tail0 (w_digits := w_digits) w_0 w_0W w_compare w_tail0
           w_add2 w_zdigits _ww_zdigits w_to_Z _ _ _ _ _ _ _);wwauto.
  exact ZnZ.spec_zdigits.
 Qed.

 Lemma spec_ww_add_mul_div : forall x y p,
       [|p|] <= Zpos _ww_digits ->
       [| add_mul_div p x y |] =
         ([|x|] * (2 ^ [|p|]) +
          [|y|] / (2 ^ ((Zpos _ww_digits) - [|p|]))) mod wwB.
 Proof.
 refine (@spec_ww_add_mul_div t w_0 w_WW w_W0 w_0W compare w_add_mul_div
              sub w_digits w_zdigits low w_to_Z
           _ _ _ _ _ _ _ _ _ _ _);wwauto.
  exact ZnZ.spec_zdigits.
 Qed.

 Let spec_ww_div_gt : forall a b,
      [|a|] > [|b|] -> 0 < [|b|] ->
      let (q,r) := div_gt a b in
      [|a|] = [|q|] * [|b|] + [|r|] /\ 0 <= [|r|] < [|b|].
 Proof.
refine
(@spec_ww_div_gt t w_digits w_0 w_WW w_0W w_compare w_eq0
   w_opp_c w_opp w_opp_carry w_sub_c w_sub w_sub_carry w_div_gt
   w_add_mul_div w_head0 w_div21 div32 _ww_zdigits ww_1 add_mul_div w_zdigits w_to_Z
 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
).
  exact ZnZ.spec_0.
  exact ZnZ.spec_to_Z.
  wwauto.
  wwauto.
  exact ZnZ.spec_compare.
  exact ZnZ.spec_eq0.
  exact ZnZ.spec_opp_c.
  exact ZnZ.spec_opp.
  exact ZnZ.spec_opp_carry.
  exact ZnZ.spec_sub_c.
  exact ZnZ.spec_sub.
  exact ZnZ.spec_sub_carry.
  exact ZnZ.spec_div_gt.
  exact ZnZ.spec_add_mul_div.
  exact ZnZ.spec_head0.
  exact ZnZ.spec_div21.
  exact spec_w_div32.
  exact ZnZ.spec_zdigits.
  exact spec_ww_digits.
  exact spec_ww_1.
  exact spec_ww_add_mul_div.
 Qed.

 Let spec_ww_div : forall a b, 0 < [|b|] ->
      let (q,r) := div a b in
      [|a|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|].
 Proof.
  refine (spec_ww_div w_digits ww_1 compare div_gt w_to_Z _ _ _ _);wwauto.
 Qed.

 Let spec_ww_mod_gt : forall a b,
      [|a|] > [|b|] -> 0 < [|b|] ->
      [|mod_gt a b|] = [|a|] mod [|b|].
 Proof.
  refine (@spec_ww_mod_gt t w_digits w_0 w_WW w_0W w_compare w_eq0
   w_opp_c w_opp w_opp_carry w_sub_c w_sub w_sub_carry w_div_gt w_mod_gt
   w_add_mul_div w_head0 w_div21 div32 _ww_zdigits ww_1 add_mul_div
   w_zdigits w_to_Z
   _ _ _ _ _   _ _ _ _ _   _ _ _ _ _   _ _ _ _ _ _ _);wwauto.
  exact ZnZ.spec_div_gt.
  exact ZnZ.spec_div21.
  exact ZnZ.spec_zdigits.
  exact spec_ww_add_mul_div.
 Qed.

 Let spec_ww_mod :  forall a b, 0 < [|b|] -> [|mod_ a b|] = [|a|] mod [|b|].
 Proof.
  refine (spec_ww_mod w_digits W0 compare mod_gt w_to_Z _ _ _);wwauto.
 Qed.

 Let spec_ww_gcd_gt : forall a b, [|a|] > [|b|] ->
      Zis_gcd [|a|] [|b|] [|gcd_gt a b|].
 Proof.
  refine (@spec_ww_gcd_gt t w_digits W0 w_to_Z _
    w_0 w_0 w_eq0 w_gcd_gt _ww_digits
  _ gcd_gt_fix _ _ _ _ gcd_cont _);wwauto.
  refine (@spec_ww_gcd_gt_aux t w_digits w_0 w_WW w_0W w_compare w_opp_c w_opp
   w_opp_carry w_sub_c w_sub w_sub_carry w_gcd_gt w_add_mul_div w_head0
   w_div21 div32 _ww_zdigits ww_1 add_mul_div w_zdigits w_to_Z
   _ _ _ _ _   _ _ _ _ _   _ _ _ _ _   _ _ _ _ _);wwauto.
  exact ZnZ.spec_div21.
  exact ZnZ.spec_zdigits.
  exact spec_ww_add_mul_div.
  refine (@spec_gcd_cont t w_digits ww_1 w_to_Z _ _ w_0 w_1 w_compare
   _ _);wwauto.
 Qed.

 Let spec_ww_gcd : forall a b, Zis_gcd [|a|] [|b|] [|gcd a b|].
 Proof.
  refine (@spec_ww_gcd t w_digits W0 compare w_to_Z _ _ w_0 w_0 w_eq0 w_gcd_gt
  _ww_digits _ gcd_gt_fix _ _ _ _ gcd_cont _);wwauto.
  refine (@spec_ww_gcd_gt_aux t w_digits w_0 w_WW w_0W w_compare w_opp_c w_opp
   w_opp_carry w_sub_c w_sub w_sub_carry w_gcd_gt w_add_mul_div w_head0
   w_div21 div32 _ww_zdigits ww_1 add_mul_div w_zdigits w_to_Z
   _ _ _ _ _   _ _ _ _ _   _ _ _ _ _   _ _ _ _ _);wwauto.
  exact ZnZ.spec_div21.
  exact ZnZ.spec_zdigits.
  exact spec_ww_add_mul_div.
  refine (@spec_gcd_cont t w_digits ww_1 w_to_Z _ _ w_0 w_1 w_compare
   _ _);wwauto.
 Qed.

 Let spec_ww_is_even : forall x,
      match is_even x with
         true => [|x|] mod 2 = 0
      | false => [|x|] mod 2 = 1
      end.
 Proof.
 refine (@spec_ww_is_even t w_is_even w_digits _ _ ).
 exact ZnZ.spec_is_even.
 Qed.

 Let spec_ww_sqrt2 : forall x y,
       wwB/ 4 <= [|x|] ->
       let (s,r) := sqrt2 x y in
          [[WW x y]] = [|s|] ^ 2 + [+|r|] /\
          [+|r|] <= 2 * [|s|].
 Proof.
 intros x y H.
 refine (@spec_ww_sqrt2 t w_is_even w_compare w_0 w_1 w_Bm1
               w_0W w_sub w_square_c w_div21 w_add_mul_div w_digits w_zdigits
               _ww_zdigits
               w_add_c w_sqrt2 w_pred pred_c pred add_c add sub_c add_mul_div
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); wwauto.
 exact ZnZ.spec_zdigits.
 exact ZnZ.spec_more_than_1_digit.
 exact ZnZ.spec_is_even.
 exact ZnZ.spec_div21.
 exact spec_ww_add_mul_div.
 exact ZnZ.spec_sqrt2.
 Qed.

 Let spec_ww_sqrt : forall x,
       [|sqrt x|] ^ 2 <= [|x|] < ([|sqrt x|] + 1) ^ 2.
 Proof.
 refine (@spec_ww_sqrt t w_is_even w_0 w_1 w_Bm1
           w_sub w_add_mul_div w_digits w_zdigits _ww_zdigits
               w_sqrt2 pred add_mul_div head0 compare
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); wwauto.
 exact ZnZ.spec_zdigits.
 exact ZnZ.spec_more_than_1_digit.
 exact ZnZ.spec_is_even.
 exact spec_ww_add_mul_div.
 exact ZnZ.spec_sqrt2.
 Qed.

 Let wB_pos : 0 < wB.
 Proof.
 unfold wB, base; apply Z.pow_pos_nonneg; auto with zarith.
 Qed.
 
 Hint Transparent ww_to_Z.

 Let ww_testbit_high n x y : Z.pos w_digits <= n ->
  Z.testbit [|WW x y|] n =
  Z.testbit (ZnZ.to_Z x) (n - Z.pos w_digits).
 Proof.
  intros Hn.
  assert (E : ZnZ.to_Z x = [|WW x y|] / wB).
  { simpl.
    rewrite Z.div_add_l; eauto with ZnZ zarith.
    now rewrite Z.div_small, Z.add_0_r; wwauto. }
  rewrite E.
  unfold wB, base. rewrite Z.div_pow2_bits.
  - f_equal; auto with zarith.
  - easy.
  - auto with zarith.
 Qed.

 Let ww_testbit_low n x y : 0 <= n < Z.pos w_digits ->
  Z.testbit [|WW x y|] n = Z.testbit (ZnZ.to_Z y) n.
 Proof.
  intros (Hn,Hn').
  assert (E : ZnZ.to_Z y = [|WW x y|] mod wB).
  { simpl; symmetry.
    rewrite Z.add_comm, Z.mod_add; auto with zarith nocore.
    apply Z.mod_small; eauto with ZnZ zarith. }
  rewrite E.
  unfold wB, base. symmetry. apply Z.mod_pow2_bits_low; auto.
 Qed.

 Let spec_lor x y : [|lor x y|] = Z.lor [|x|] [|y|].
 Proof.
  destruct x as [ |hx lx]. trivial.
  destruct y as [ |hy ly]. now rewrite Z.lor_comm.
  change ([|WW (ZnZ.lor hx hy) (ZnZ.lor lx ly)|] =
          Z.lor [|WW hx lx|] [|WW hy ly|]).
  apply Z.bits_inj'; intros n Hn.
  rewrite Z.lor_spec.
  destruct (Z.le_gt_cases (Z.pos w_digits) n) as [LE|GT].
  - now rewrite !ww_testbit_high, ZnZ.spec_lor, Z.lor_spec.
  - rewrite !ww_testbit_low; auto.
    now rewrite ZnZ.spec_lor, Z.lor_spec.
 Qed.

 Let spec_land x y : [|land x y|] = Z.land [|x|] [|y|].
 Proof.
  destruct x as [ |hx lx]. trivial.
  destruct y as [ |hy ly]. now rewrite Z.land_comm.
  change ([|WW (ZnZ.land hx hy) (ZnZ.land lx ly)|] =
          Z.land [|WW hx lx|] [|WW hy ly|]).
  apply Z.bits_inj'; intros n Hn.
  rewrite Z.land_spec.
  destruct (Z.le_gt_cases (Z.pos w_digits) n) as [LE|GT].
  - now rewrite !ww_testbit_high, ZnZ.spec_land, Z.land_spec.
  - rewrite !ww_testbit_low; auto.
    now rewrite ZnZ.spec_land, Z.land_spec.
 Qed.

 Let spec_lxor x y : [|lxor x y|] = Z.lxor [|x|] [|y|].
 Proof.
  destruct x as [ |hx lx]. trivial.
  destruct y as [ |hy ly]. now rewrite Z.lxor_comm.
  change ([|WW (ZnZ.lxor hx hy) (ZnZ.lxor lx ly)|] =
          Z.lxor [|WW hx lx|] [|WW hy ly|]).
  apply Z.bits_inj'; intros n Hn.
  rewrite Z.lxor_spec.
  destruct (Z.le_gt_cases (Z.pos w_digits) n) as [LE|GT].
  - now rewrite !ww_testbit_high, ZnZ.spec_lxor, Z.lxor_spec.
  - rewrite !ww_testbit_low; auto.
    now rewrite ZnZ.spec_lxor, Z.lxor_spec.
 Qed.

 Global Instance mk_zn2z_specs : ZnZ.Specs mk_zn2z_ops.
 Proof.
  apply ZnZ.MkSpecs; auto.
  exact spec_ww_add_mul_div.

  refine (@spec_ww_pos_mod t w_0 w_digits w_zdigits w_WW
           w_pos_mod compare w_0W low sub _ww_zdigits w_to_Z
       _ _ _ _ _ _ _ _ _ _ _ _);wwauto.
  exact ZnZ.spec_zdigits.
  unfold w_to_Z, w_zdigits.
  rewrite ZnZ.spec_zdigits.
  rewrite <- Pos2Z.inj_xO; exact spec_ww_digits.
 Qed.

 Global Instance mk_zn2z_specs_karatsuba : ZnZ.Specs mk_zn2z_ops_karatsuba.
 Proof.
  apply ZnZ.MkSpecs; auto.
  exact spec_ww_add_mul_div.
  refine (@spec_ww_pos_mod t w_0 w_digits w_zdigits w_WW
           w_pos_mod compare w_0W low sub _ww_zdigits w_to_Z
       _ _ _ _ _ _ _ _ _ _ _ _);wwauto.
  exact ZnZ.spec_zdigits.
  unfold w_to_Z, w_zdigits.
  rewrite ZnZ.spec_zdigits.
  rewrite <- Pos2Z.inj_xO; exact spec_ww_digits.
 Qed.

End Z_2nZ.


Section MulAdd.

  Context {t : Type}{ops : ZnZ.Ops t}{specs : ZnZ.Specs ops}.

  Definition mul_add:= w_mul_add ZnZ.zero ZnZ.succ ZnZ.add_c ZnZ.mul_c.

  Notation "[| x |]" := (ZnZ.to_Z x)  (at level 0, x at level 99).

  Notation "[|| x ||]" :=
   (zn2z_to_Z (base ZnZ.digits) ZnZ.to_Z x)  (at level 0, x at level 99).

  Lemma spec_mul_add: forall x y z,
     let (zh, zl) := mul_add x y z in
  [||WW zh zl||] = [|x|] * [|y|] + [|z|].
  Proof.
  intros x y z.
   refine (spec_w_mul_add _ _ _ _ _ _ _ _ _ _ _ _ x y z); auto.
  exact ZnZ.spec_0.
  exact ZnZ.spec_to_Z.
  exact ZnZ.spec_succ.
  exact ZnZ.spec_add_c.
  exact ZnZ.spec_mul_c.
  Qed.

End MulAdd.


(** Modular versions of DoubleCyclic *)

Module DoubleCyclic (C:CyclicType) <: CyclicType.
 Definition t := zn2z C.t.
 Instance ops : ZnZ.Ops t := mk_zn2z_ops.
 Instance specs : ZnZ.Specs ops := mk_zn2z_specs.
End DoubleCyclic.

Module DoubleCyclicKaratsuba (C:CyclicType) <: CyclicType.
 Definition t := zn2z C.t.
 Definition ops : ZnZ.Ops t := mk_zn2z_ops_karatsuba.
 Definition specs : ZnZ.Specs ops := mk_zn2z_specs_karatsuba.
End DoubleCyclicKaratsuba.

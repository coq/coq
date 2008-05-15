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
Require Import Basic_type.
Require Import GenBase.
Require Import GenAdd.
Require Import GenSub.
Require Import GenMul.
Require Import GenSqrt.
Require Import GenLift.
Require Import GenDivn1.
Require Import GenDiv. 
Require Import ZnZ.

Open Local Scope Z_scope.


Section Zn2Z.
 
 Variable w : Set.
 Variable w_op : znz_op w.
 Let w_digits      := w_op.(znz_digits).
 Let w_zdigits      := w_op.(znz_zdigits).

 Let w_to_Z        := w_op.(znz_to_Z).
 Let w_of_pos      := w_op.(znz_of_pos).
 Let w_head0       := w_op.(znz_head0).
 Let w_tail0       := w_op.(znz_tail0).

 Let w_0            := w_op.(znz_0).
 Let w_1            := w_op.(znz_1).
 Let w_Bm1          := w_op.(znz_Bm1).

 Let w_WW           := w_op.(znz_WW).
 Let w_W0           := w_op.(znz_W0).
 Let w_0W           := w_op.(znz_0W).

 Let w_compare     := w_op.(znz_compare).
 Let w_eq0         := w_op.(znz_eq0).

 Let w_opp_c       := w_op.(znz_opp_c).
 Let w_opp         := w_op.(znz_opp).
 Let w_opp_carry   := w_op.(znz_opp_carry).

 Let w_succ_c      := w_op.(znz_succ_c).
 Let w_add_c       := w_op.(znz_add_c).
 Let w_add_carry_c := w_op.(znz_add_carry_c).
 Let w_succ        := w_op.(znz_succ).
 Let w_add         := w_op.(znz_add).
 Let w_add_carry   := w_op.(znz_add_carry).

 Let w_pred_c      := w_op.(znz_pred_c).
 Let w_sub_c       := w_op.(znz_sub_c).
 Let w_sub_carry_c := w_op.(znz_sub_carry_c).
 Let w_pred        := w_op.(znz_pred).
 Let w_sub         := w_op.(znz_sub).
 Let w_sub_carry   := w_op.(znz_sub_carry).


 Let w_mul_c       := w_op.(znz_mul_c).
 Let w_mul         := w_op.(znz_mul).
 Let w_square_c    := w_op.(znz_square_c).

 Let w_div21       := w_op.(znz_div21).
 Let w_div_gt      := w_op.(znz_div_gt).
 Let w_div         := w_op.(znz_div).

 Let w_mod_gt      := w_op.(znz_mod_gt).
 Let w_mod         := w_op.(znz_mod).

 Let w_gcd_gt      := w_op.(znz_gcd_gt).
 Let w_gcd         := w_op.(znz_gcd).

 Let w_add_mul_div := w_op.(znz_add_mul_div). 

 Let w_pos_mod := w_op.(znz_pos_mod).

 Let w_is_even     := w_op.(znz_is_even).
 Let w_sqrt2       := w_op.(znz_sqrt2).
 Let w_sqrt        := w_op.(znz_sqrt).

 Let _zn2z := zn2z w.

 Let wB := base w_digits.

 Let w_Bm2 := w_pred w_Bm1.
 
 Let ww_1 := ww_1 w_0 w_1.
 Let ww_Bm1 := ww_Bm1 w_Bm1.

 Let w_add2 a b := match w_add_c a b with C0 p => WW w_0 p | C1 p => WW w_1 p end.

 Let _ww_digits := xO w_digits.

 Let _ww_zdigits := w_add2 w_zdigits w_zdigits.

 Let to_Z := zn2z_to_Z wB w_to_Z.

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

 Let ww_WW := Eval lazy beta delta [ww_WW] in (@ww_WW w).
 Let ww_0W := Eval lazy beta delta [ww_0W] in (@ww_0W w).
 Let ww_W0 := Eval lazy beta delta [ww_W0] in (@ww_W0 w).

 (* ** Comparison ** *)
 Let compare :=
  Eval lazy beta delta[ww_compare] in ww_compare w_0 w_compare.

 Let eq0 (x:zn2z w) := 
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
  Eval lazy beta iota delta [ww_mul_c gen_mul_c] in
  ww_mul_c w_0 w_1 w_WW w_W0 w_mul_c add_c add add_carry.

 Let karatsuba_c :=
  Eval lazy beta iota delta [ww_karatsuba_c gen_mul_c kara_prod] in
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

 Let low (p: zn2z w) := match p with WW _ p1 => p1 | _ => w_0 end.

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

 (* ** Record of operators on 2 words *)
   
 Definition mk_zn2z_op := 
  mk_znz_op _ww_digits _ww_zdigits
    to_Z ww_of_pos head0 tail0
    W0 ww_1 ww_Bm1
    ww_WW ww_W0 ww_0W  
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
    sqrt.

 Definition mk_zn2z_op_karatsuba := 
   mk_znz_op _ww_digits _ww_zdigits
    to_Z ww_of_pos head0 tail0
    W0 ww_1 ww_Bm1
    ww_WW ww_W0 ww_0W  
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
    sqrt.

 (* Proof *)
 Variable op_spec : znz_spec w_op.

 Hint Resolve 
    (spec_to_Z op_spec)
    (spec_of_pos op_spec)
    (spec_0 op_spec)
    (spec_1 op_spec)
    (spec_Bm1 op_spec)
    (spec_WW op_spec)
    (spec_0W op_spec)
    (spec_W0 op_spec)
    (spec_compare op_spec)
    (spec_eq0 op_spec)
    (spec_opp_c op_spec)
    (spec_opp op_spec)
    (spec_opp_carry op_spec)
    (spec_succ_c op_spec)
    (spec_add_c op_spec)
    (spec_add_carry_c op_spec)
    (spec_succ op_spec)
    (spec_add op_spec)
    (spec_add_carry op_spec)
    (spec_pred_c op_spec)
    (spec_sub_c op_spec)
    (spec_sub_carry_c op_spec)
    (spec_pred op_spec)
    (spec_sub op_spec)
    (spec_sub_carry op_spec)
    (spec_mul_c op_spec)
    (spec_mul op_spec)
    (spec_square_c op_spec)
    (spec_div21 op_spec)
    (spec_div_gt op_spec)
    (spec_div op_spec)    
    (spec_mod_gt op_spec)
    (spec_mod op_spec)      
    (spec_gcd_gt op_spec)
    (spec_gcd op_spec) 
    (spec_head0 op_spec) 
    (spec_tail0 op_spec) 
    (spec_add_mul_div op_spec)
    (spec_pos_mod)
    (spec_is_even)
    (spec_sqrt2)
    (spec_sqrt).

 Let wwB := base _ww_digits.

 Notation "[| x |]" := (to_Z x)  (at level 0, x at level 99).

 Notation "[+| c |]" :=
   (interp_carry 1 wwB to_Z c)  (at level 0, x at level 99).

 Notation "[-| c |]" :=
   (interp_carry (-1) wwB to_Z c)  (at level 0, x at level 99).

 Notation "[[ x ]]" := (zn2z_to_Z wwB to_Z x)  (at level 0, x at level 99).

 Let spec_ww_to_Z   : forall x, 0 <= [| x |] < wwB.
 Proof. refine (spec_ww_to_Z w_digits w_to_Z _);auto. Qed.

 Let spec_ww_of_pos : forall p,
     Zpos p = (Z_of_N (fst (ww_of_pos p)))*wwB + [|(snd (ww_of_pos p))|].
 Proof.
  unfold ww_of_pos;intros.
  assert (H:= spec_of_pos op_spec p);unfold w_of_pos;
   destruct (znz_of_pos w_op p). simpl in H.
  rewrite H;clear H;destruct n;simpl to_Z.
  simpl;unfold w_to_Z,w_0;rewrite (spec_0 op_spec);trivial.
  unfold Z_of_N; assert (H:= spec_of_pos op_spec p0);
  destruct (znz_of_pos w_op p0). simpl in H.
  rewrite H;unfold fst, snd,Z_of_N, w_WW, to_Z.
  rewrite (spec_WW op_spec). replace wwB with (wB*wB).
  unfold wB,w_digits;clear H;destruct n;ring.
  symmetry. rewrite <- Zpower_2; exact (wwB_wBwB w_digits).
 Qed.

 Let spec_ww_0 : [|W0|] = 0.
 Proof. reflexivity. Qed.

 Let spec_ww_1 : [|ww_1|] = 1.
 Proof. refine (spec_ww_1 w_0 w_1 w_digits w_to_Z _ _);auto. Qed.

 Let spec_ww_Bm1 : [|ww_Bm1|] = wwB - 1.
 Proof. refine (spec_ww_Bm1 w_Bm1 w_digits w_to_Z _);auto. Qed.

 Let spec_ww_WW  : forall h l, [[ww_WW h l]] = [|h|] * wwB + [|l|].
 Proof. 
  intros h l. replace wwB with (wB*wB). destruct h;simpl.
  destruct l;simpl;ring. ring.
  symmetry. rewrite <- Zpower_2; exact (wwB_wBwB w_digits).
 Qed.

 Let spec_ww_0W  : forall l, [[ww_0W l]] = [|l|].
 Proof. 
  intros l. replace wwB with (wB*wB). 
  destruct l;simpl;ring. 
  symmetry. ring_simplify; exact (wwB_wBwB w_digits).
 Qed.

 Let spec_ww_W0  : forall h, [[ww_W0 h]] = [|h|]*wwB.
 Proof.
  intros h. replace wwB with (wB*wB). 
  destruct h;simpl;ring. 
  symmetry. ring_simplify; exact (wwB_wBwB w_digits).
 Qed.

 Let spec_ww_compare : 
     forall x y,
       match compare x y with
       | Eq => [|x|] = [|y|]
       | Lt => [|x|] < [|y|]
       | Gt => [|x|] > [|y|]
       end.
 Proof. 
  refine (spec_ww_compare w_0 w_digits w_to_Z w_compare _ _ _);auto. 
  exact (spec_compare op_spec). 
 Qed.

 Let spec_ww_eq0 : forall x, eq0 x = true -> [|x|] = 0.
 Proof. destruct x;simpl;intros;trivial;discriminate. Qed. 

 Let spec_ww_opp_c : forall x, [-|opp_c x|] = -[|x|].
 Proof.
  refine(spec_ww_opp_c w_0 w_0 W0 w_opp_c w_opp_carry w_digits w_to_Z _ _ _ _);
  auto.
 Qed.

 Let spec_ww_opp : forall x, [|opp x|] = (-[|x|]) mod wwB.
 Proof.
  refine(spec_ww_opp w_0 w_0 W0 w_opp_c w_opp_carry w_opp 
   w_digits w_to_Z _ _ _ _ _);
  auto.
 Qed.

 Let spec_ww_opp_carry : forall x, [|opp_carry x|] = wwB - [|x|] - 1.
 Proof.
  refine (spec_ww_opp_carry w_WW ww_Bm1 w_opp_carry w_digits w_to_Z _ _ _);
  auto. exact (spec_WW op_spec).
 Qed.

 Let spec_ww_succ_c : forall x, [+|succ_c x|] = [|x|] + 1.
 Proof.
  refine (spec_ww_succ_c w_0 w_0 ww_1 w_succ_c w_digits w_to_Z _ _ _ _);auto.
 Qed.

 Let spec_ww_add_c  : forall x y, [+|add_c x y|] = [|x|] + [|y|].
 Proof.
  refine (spec_ww_add_c w_WW w_add_c w_add_carry_c w_digits w_to_Z _ _ _);auto.
  exact (spec_WW op_spec).
 Qed.

 Let spec_ww_add_carry_c : forall x y, [+|add_carry_c x y|] = [|x|]+[|y|]+1.
 Proof.
  refine (spec_ww_add_carry_c w_0 w_0 w_WW ww_1 w_succ_c w_add_c w_add_carry_c
   w_digits w_to_Z _ _ _ _ _ _ _);auto. exact (spec_WW op_spec).
 Qed.

 Let spec_ww_succ : forall x, [|succ x|] = ([|x|] + 1) mod wwB.
 Proof.
  refine (spec_ww_succ w_W0 ww_1 w_succ_c w_succ w_digits w_to_Z _ _ _ _ _);
  auto. exact (spec_W0 op_spec).
 Qed.

 Let spec_ww_add : forall x y, [|add x y|] = ([|x|] + [|y|]) mod wwB.
 Proof.
  refine (spec_ww_add w_add_c w_add w_add_carry w_digits w_to_Z _ _ _ _);auto.
 Qed.

 Let spec_ww_add_carry : forall x y, [|add_carry x y|]=([|x|]+[|y|]+1)mod wwB.
 Proof.
  refine (spec_ww_add_carry w_W0 ww_1 w_succ_c w_add_carry_c w_succ 
  w_add w_add_carry w_digits w_to_Z _ _ _ _ _ _ _ _);auto.
  exact (spec_W0 op_spec).
 Qed.

 Let spec_ww_pred_c : forall x, [-|pred_c x|] = [|x|] - 1.
 Proof.
  refine (spec_ww_pred_c w_0 w_Bm1 w_WW ww_Bm1 w_pred_c w_digits w_to_Z 
   _ _ _ _ _);auto. exact (spec_WW op_spec).
 Qed.

 Let spec_ww_sub_c : forall x y, [-|sub_c x y|] = [|x|] - [|y|].
 Proof.
  refine (spec_ww_sub_c w_0 w_0 w_WW W0 w_opp_c w_opp_carry w_sub_c 
   w_sub_carry_c w_digits w_to_Z _ _ _ _ _ _ _);auto. exact (spec_WW op_spec). 
 Qed.

 Let spec_ww_sub_carry_c : forall x y, [-|sub_carry_c x y|] = [|x|]-[|y|]-1.
 Proof.
  refine (spec_ww_sub_carry_c w_0 w_Bm1 w_WW ww_Bm1 w_opp_carry w_pred_c 
   w_sub_c w_sub_carry_c w_digits w_to_Z _ _ _ _ _ _ _ _);auto.
  exact (spec_WW op_spec). 
 Qed.

 Let spec_ww_pred : forall x, [|pred x|] = ([|x|] - 1) mod wwB.
 Proof.
  refine (spec_ww_pred w_0 w_Bm1 w_WW ww_Bm1 w_pred_c w_pred w_digits w_to_Z
   _ _ _ _ _ _);auto. exact (spec_WW op_spec). 
 Qed.

 Let spec_ww_sub : forall x y, [|sub x y|] = ([|x|] - [|y|]) mod wwB.
 Proof.
  refine (spec_ww_sub w_0 w_0 w_WW W0 w_opp_c w_opp_carry w_sub_c w_opp
   w_sub w_sub_carry w_digits w_to_Z _ _ _ _ _ _ _ _ _);auto.
  exact (spec_WW op_spec). 
 Qed.

 Let spec_ww_sub_carry : forall x y, [|sub_carry x y|]=([|x|]-[|y|]-1) mod wwB.
 Proof.
  refine (spec_ww_sub_carry w_0 w_Bm1 w_WW ww_Bm1 w_opp_carry w_pred_c
   w_sub_carry_c w_pred w_sub w_sub_carry w_digits w_to_Z _ _ _ _ _ _ _ _ _ _);
  auto.   exact (spec_WW op_spec). 
 Qed.

 Let spec_ww_mul_c : forall x y, [[mul_c x y ]] = [|x|] * [|y|].
 Proof.
  refine (spec_ww_mul_c w_0 w_1 w_WW w_W0 w_mul_c add_c add add_carry w_digits
   w_to_Z _ _ _ _ _ _ _ _ _);auto. exact (spec_WW op_spec).  
  exact (spec_W0 op_spec). exact (spec_mul_c op_spec).
 Qed.

 Let spec_ww_karatsuba_c : forall x y, [[karatsuba_c x y ]] = [|x|] * [|y|].
 Proof.
 refine (spec_ww_karatsuba_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          _ _ _ _ _ _ _ _ _ _ _ _); auto.
  unfold w_digits; apply spec_more_than_1_digit; auto.
  exact (spec_WW op_spec).  
  exact (spec_W0 op_spec). 
  exact (spec_compare op_spec).
  exact (spec_mul_c op_spec).
 Qed. 

 Let spec_ww_mul : forall x y, [|mul x y|] = ([|x|] * [|y|]) mod wwB.
 Proof.
  refine (spec_ww_mul w_W0 w_add w_mul_c w_mul add w_digits w_to_Z _ _ _ _ _);
  auto. exact (spec_W0 op_spec). exact (spec_mul_c op_spec).
 Qed.

 Let spec_ww_square_c : forall x, [[square_c x]] = [|x|] * [|x|].
 Proof.
  refine (spec_ww_square_c w_0 w_1 w_WW w_W0 w_mul_c w_square_c add_c add 
   add_carry w_digits w_to_Z _ _ _ _ _ _ _ _ _ _);auto.
  exact (spec_WW op_spec). exact (spec_W0 op_spec).
  exact (spec_mul_c op_spec). exact (spec_square_c op_spec).
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
   _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);auto.
  unfold w_Bm2, w_to_Z, w_pred, w_Bm1.
  rewrite (spec_pred op_spec);rewrite (spec_Bm1 op_spec).
  unfold w_digits;rewrite Zmod_small. ring.
  assert (H:= wB_pos(znz_digits w_op)). omega.
  exact (spec_WW op_spec). exact (spec_compare op_spec).
  exact (spec_mul_c op_spec).  exact (spec_div21 op_spec).
 Qed.

 Let spec_ww_div21 : forall a1 a2 b,
      wwB/2 <= [|b|] ->
      [|a1|] < [|b|] ->
      let (q,r) := div21 a1 a2 b in
      [|a1|] *wwB+ [|a2|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|].
 Proof.
  refine (spec_ww_div21 w_0 w_0W div32 ww_1 compare sub w_digits w_to_Z
   _ _ _ _ _ _ _);auto. exact (spec_0W op_spec).
 Qed.

 Let spec_add2: forall x y,
  [|w_add2 x y|] = w_to_Z x + w_to_Z y.
  unfold w_add2.
  intros xh xl; generalize (spec_add_c op_spec xh xl).
  unfold w_add_c; case znz_add_c; unfold interp_carry; simpl ww_to_Z.
    intros w0 Hw0; simpl; unfold w_to_Z; rewrite Hw0.
  unfold w_0; rewrite spec_0; simpl; auto with zarith.
  intros w0; rewrite Zmult_1_l; simpl.
  unfold w_to_Z, w_1; rewrite spec_1; auto with zarith.
  rewrite Zmult_1_l; auto.
 Qed.

 Let spec_low: forall x,
  w_to_Z (low x) = [|x|] mod wB.
  intros x; case x; simpl low.
    unfold ww_to_Z, w_to_Z, w_0; rewrite (spec_0 op_spec); simpl.
    rewrite Zmod_small; auto with zarith.
    split; auto with zarith.
    unfold wB, base; auto with zarith.
  intros xh xl; simpl.
  rewrite Zplus_comm; rewrite Z_mod_plus; auto with zarith.
  rewrite Zmod_small; auto with zarith.
  unfold wB, base; auto with zarith.
 Qed.

 Let spec_ww_digits: 
  [|_ww_zdigits|] = Zpos (xO w_digits).
 Proof.
 unfold w_to_Z, _ww_zdigits.
 rewrite spec_add2.
 unfold w_to_Z, w_zdigits, w_digits.
 rewrite spec_zdigits; auto.
 rewrite Zpos_xO; auto with zarith.
 Qed.


 Let spec_ww_head00  : forall x,  [|x|] = 0 -> [|head0 x|] = Zpos _ww_digits.
 Proof.
 refine (spec_ww_head00 w_0 w_0W 
                w_compare w_head0 w_add2 w_zdigits _ww_zdigits
                w_to_Z _ _ _ (refl_equal _ww_digits) _ _ _ _); auto.
 exact (spec_compare op_spec).
 exact (spec_head00 op_spec).
 exact (spec_zdigits op_spec).
 Qed.

 Let spec_ww_head0  : forall x,  0 < [|x|] ->
	 wwB/ 2 <= 2 ^ [|head0 x|] * [|x|] < wwB.
 Proof.
  refine (spec_ww_head0 w_0 w_0W w_compare w_head0 
           w_add2 w_zdigits _ww_zdigits 
   w_to_Z _ _ _ _ _ _ _);auto.
  exact (spec_0W op_spec).
  exact (spec_compare op_spec).
  exact (spec_zdigits op_spec).
 Qed.

 Let spec_ww_tail00  : forall x,  [|x|] = 0 -> [|tail0 x|] = Zpos _ww_digits.
 Proof.
 refine (spec_ww_tail00 w_0 w_0W 
                w_compare w_tail0 w_add2 w_zdigits _ww_zdigits
                w_to_Z _ _ _ (refl_equal _ww_digits) _ _ _ _); auto.
 exact (spec_compare op_spec).
 exact (spec_tail00 op_spec).
 exact (spec_zdigits op_spec).
 Qed.


 Let spec_ww_tail0  : forall x,  0 < [|x|] ->
  exists y, 0 <= y /\ [|x|] = (2 * y + 1) * 2 ^ [|tail0 x|].
 Proof.
  refine (spec_ww_tail0 (w_digits := w_digits) w_0 w_0W w_compare w_tail0 
           w_add2 w_zdigits _ww_zdigits w_to_Z _ _ _ _ _ _ _);auto.
  exact (spec_0W op_spec).
  exact (spec_compare op_spec).
  exact (spec_zdigits op_spec).
 Qed.

 Lemma spec_ww_add_mul_div : forall x y p,
       [|p|] <= Zpos _ww_digits ->
       [| add_mul_div p x y |] =
         ([|x|] * (2 ^ [|p|]) +
          [|y|] / (2 ^ ((Zpos _ww_digits) - [|p|]))) mod wwB.
 Proof.
 refine (@spec_ww_add_mul_div w w_0 w_WW w_W0 w_0W compare w_add_mul_div 
              sub w_digits w_zdigits low w_to_Z
           _ _ _ _ _ _ _ _ _ _ _);auto.
  exact (spec_WW op_spec). 
  exact (spec_W0 op_spec).
  exact (spec_0W op_spec).
  exact (spec_zdigits op_spec).
 Qed.

 Let spec_ww_div_gt : forall a b, 
      [|a|] > [|b|] -> 0 < [|b|] ->
      let (q,r) := div_gt a b in
      [|a|] = [|q|] * [|b|] + [|r|] /\ 0 <= [|r|] < [|b|].
 Proof.
refine 
(@spec_ww_div_gt w w_digits w_0 w_WW w_0W w_compare w_eq0 
   w_opp_c w_opp w_opp_carry w_sub_c w_sub w_sub_carry w_div_gt
   w_add_mul_div w_head0 w_div21 div32 _ww_zdigits ww_1 add_mul_div w_zdigits w_to_Z
 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
).
  exact (spec_0 op_spec).
  exact (spec_to_Z op_spec).
  exact (spec_WW op_spec). 
  exact (spec_0W op_spec). 
  exact (spec_compare op_spec).
  exact (spec_eq0 op_spec).
  exact (spec_opp_c op_spec).
  exact (spec_opp op_spec).
  exact (spec_opp_carry op_spec).
  exact (spec_sub_c op_spec).
  exact (spec_sub op_spec).
  exact (spec_sub_carry op_spec).
  exact (spec_div_gt op_spec).
  exact (spec_add_mul_div op_spec).
  exact (spec_head0 op_spec).
  exact (spec_div21 op_spec).
  exact spec_w_div32.
  exact (spec_zdigits op_spec).
  exact spec_ww_digits.
  exact spec_ww_1.
  exact spec_ww_add_mul_div.
 Qed.

 Let spec_ww_div : forall a b, 0 < [|b|] ->
      let (q,r) := div a b in
      [|a|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|].
 Proof.
  refine (spec_ww_div w_digits ww_1 compare div_gt w_to_Z _ _ _ _);auto.
 Qed.

 Let spec_ww_mod_gt : forall a b, 
      [|a|] > [|b|] -> 0 < [|b|] ->
      [|mod_gt a b|] = [|a|] mod [|b|].
 Proof.
  refine (@spec_ww_mod_gt w w_digits w_0 w_WW w_0W w_compare w_eq0 
   w_opp_c w_opp w_opp_carry w_sub_c w_sub w_sub_carry w_div_gt w_mod_gt
   w_add_mul_div w_head0 w_div21 div32 _ww_zdigits ww_1 add_mul_div 
   w_zdigits w_to_Z 
   _ _ _ _ _   _ _ _ _ _   _ _ _ _ _   _ _ _ _ _ _ _);auto.
  exact (spec_WW op_spec). 
  exact (spec_0W op_spec). 
  exact (spec_compare op_spec).
  exact (spec_div_gt op_spec).
  exact (spec_div21 op_spec).
  exact (spec_zdigits op_spec).
  exact spec_ww_add_mul_div.
 Qed.

 Let spec_ww_mod :  forall a b, 0 < [|b|] -> [|mod_ a b|] = [|a|] mod [|b|].
 Proof.
  refine (spec_ww_mod w_digits W0 compare mod_gt w_to_Z _ _ _);auto.
 Qed.

 Let spec_ww_gcd_gt : forall a b, [|a|] > [|b|] ->
      Zis_gcd [|a|] [|b|] [|gcd_gt a b|].
 Proof.
  refine (@spec_ww_gcd_gt w w_digits W0 w_to_Z _ 
    w_0 w_0 w_eq0 w_gcd_gt _ww_digits
  _ gcd_gt_fix _ _ _ _ gcd_cont _);auto.
  refine (@spec_ww_gcd_gt_aux w w_digits w_0 w_WW w_0W w_compare w_opp_c w_opp
   w_opp_carry w_sub_c w_sub w_sub_carry w_gcd_gt w_add_mul_div w_head0
   w_div21 div32 _ww_zdigits ww_1 add_mul_div w_zdigits w_to_Z 
   _ _ _ _ _   _ _ _ _ _   _ _ _ _ _   _ _ _ _ _);auto.
  exact (spec_WW op_spec). 
  exact (spec_0W op_spec). 
  exact (spec_compare op_spec).
  exact (spec_div21 op_spec).
  exact (spec_zdigits op_spec).
  exact spec_ww_add_mul_div.
  refine (@spec_gcd_cont w w_digits ww_1 w_to_Z _ _ w_0 w_1 w_compare
   _ _);auto.
 exact (spec_compare op_spec).
 Qed.

 Let spec_ww_gcd : forall a b, Zis_gcd [|a|] [|b|] [|gcd a b|].
 Proof.
  refine (@spec_ww_gcd w w_digits W0 compare w_to_Z _ _ w_0 w_0 w_eq0 w_gcd_gt
  _ww_digits _ gcd_gt_fix _ _ _ _ gcd_cont _);auto.
  refine (@spec_ww_gcd_gt_aux w w_digits w_0 w_WW w_0W w_compare w_opp_c w_opp
   w_opp_carry w_sub_c w_sub w_sub_carry w_gcd_gt w_add_mul_div w_head0
   w_div21 div32 _ww_zdigits ww_1 add_mul_div w_zdigits w_to_Z 
   _ _ _ _ _   _ _ _ _ _   _ _ _ _ _   _ _ _ _ _);auto.
  exact (spec_WW op_spec).
  exact (spec_0W op_spec).
  exact (spec_compare op_spec).
  exact (spec_div21 op_spec).
  exact (spec_zdigits op_spec).
  exact spec_ww_add_mul_div.
  refine (@spec_gcd_cont w w_digits ww_1 w_to_Z _ _ w_0 w_1 w_compare
   _ _);auto.
  exact (spec_compare op_spec).
 Qed.

 Let spec_ww_is_even : forall x,
      match is_even x with
         true => [|x|] mod 2 = 0
      | false => [|x|] mod 2 = 1
      end.
 Proof.
 refine (@spec_ww_is_even w w_is_even w_0 w_1 w_Bm1 w_digits _ _ _ _ _); auto.
 exact (spec_is_even op_spec).
 Qed.

 Let spec_ww_sqrt2 : forall x y,
       wwB/ 4 <= [|x|] ->
       let (s,r) := sqrt2 x y in
          [[WW x y]] = [|s|] ^ 2 + [+|r|] /\
          [+|r|] <= 2 * [|s|].
 Proof.
 intros x y H.
 refine (@spec_ww_sqrt2 w w_is_even w_compare w_0 w_1 w_Bm1
               w_0W w_sub w_square_c w_div21 w_add_mul_div w_digits w_zdigits
               _ww_zdigits
               w_add_c w_sqrt2 w_pred pred_c pred add_c add sub_c add_mul_div
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); auto.
 exact (spec_zdigits op_spec).
 exact (spec_more_than_1_digit op_spec).
 exact (spec_0W op_spec).
 exact (spec_is_even op_spec).
 exact (spec_compare op_spec).
 exact (spec_square_c op_spec).
 exact (spec_div21 op_spec).
 exact (spec_ww_add_mul_div).
 exact (spec_sqrt2 op_spec).
 Qed.

 Let spec_ww_sqrt : forall x,
       [|sqrt x|] ^ 2 <= [|x|] < ([|sqrt x|] + 1) ^ 2.
 Proof.
 refine (@spec_ww_sqrt w w_is_even w_0 w_1 w_Bm1 
           w_sub w_add_mul_div w_digits w_zdigits _ww_zdigits
               w_sqrt2 pred add_mul_div head0 compare
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); auto.
 exact (spec_zdigits op_spec).
 exact (spec_more_than_1_digit op_spec).
 exact (spec_is_even op_spec).
 exact (spec_ww_add_mul_div).
 exact (spec_sqrt2 op_spec).
 Qed.

 Lemma mk_znz2_spec : znz_spec mk_zn2z_op.
 Proof.
  apply mk_znz_spec;auto.
  exact spec_ww_add_mul_div.

  refine (@spec_ww_pos_mod w w_0 w_digits w_zdigits w_WW 
           w_pos_mod compare w_0W low sub _ww_zdigits w_to_Z
       _ _ _ _ _ _ _ _ _ _ _ _);auto.
  exact (spec_WW op_spec).
  exact (spec_pos_mod op_spec).
  exact (spec_0W op_spec).
  exact (spec_zdigits op_spec).
  unfold w_to_Z, w_zdigits.
  rewrite (spec_zdigits op_spec).
  rewrite <- Zpos_xO; exact spec_ww_digits.
 Qed.

 Lemma mk_znz2_karatsuba_spec : znz_spec mk_zn2z_op_karatsuba.
 Proof.
  apply mk_znz_spec;auto.
  exact spec_ww_add_mul_div.
  refine (@spec_ww_pos_mod w w_0 w_digits w_zdigits w_WW 
           w_pos_mod compare w_0W low sub _ww_zdigits w_to_Z
       _ _ _ _ _ _ _ _ _ _ _ _);auto.
  exact (spec_WW op_spec).
  exact (spec_pos_mod op_spec).
  exact (spec_0W op_spec).
  exact (spec_zdigits op_spec).
  unfold w_to_Z, w_zdigits.
  rewrite (spec_zdigits op_spec).
  rewrite <- Zpos_xO; exact spec_ww_digits.
 Qed.
End Zn2Z. 
 
Section MulAdd.
 
  Variable w: Set.
  Variable op: znz_op w.
  Variable sop: znz_spec op.

  Definition mul_add:= w_mul_add (znz_0 op) (znz_succ op) (znz_add_c op) (znz_mul_c op).

  Notation "[| x |]" := (znz_to_Z op x)  (at level 0, x at level 99).

  Notation "[|| x ||]" :=
   (zn2z_to_Z (base (znz_digits op)) (znz_to_Z op) x)  (at level 0, x at level 99).


  Lemma spec_mul_add: forall x y z,
     let (zh, zl) := mul_add x y z in
  [||WW zh zl||] = [|x|] * [|y|] + [|z|].
  Proof.
  intros x y z.
   refine (spec_w_mul_add _ _ _ _ _ _ _ _ _ _ _ _ x y z); auto.
  exact (spec_0 sop).
  exact (spec_to_Z sop).
  exact (spec_succ sop).
  exact (spec_add_c sop).
  exact (spec_mul_c sop).
  Qed.

End MulAdd.



 

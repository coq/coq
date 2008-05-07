(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*        Benjamin Gregoire, INRIA          Laurent Thery, INRIA        *)
(************************************************************************)

(* $Id$ *)

(** * Signature and specification of a bounded integer structure *)

(** 
- Authors: Benjamin Grégoire, Laurent Théry
- Institution: INRIA
- Date: 2007
*)

Set Implicit Arguments.

Require Import ZArith.
Require Import Znumtheory.
Require Import Basic_type.
Require Import GenBase.

Open Local Scope Z_scope.

Section ZnZ_Op.

 Variable znz : Set.

 Record znz_op : Set := mk_znz_op {

    (* Conversion functions with Z *)
    znz_digits : positive;
    znz_zdigits: znz;
    znz_to_Z   : znz -> Z;
    znz_of_pos : positive -> N * znz;
    znz_head0  : znz -> znz;
    znz_tail0  : znz -> znz;

    (* Basic constructors *)
    znz_0   : znz;
    znz_1   : znz;
    znz_Bm1 : znz;
    znz_WW  : znz -> znz -> zn2z znz;
    znz_W0  : znz -> zn2z znz;
    znz_0W  : znz -> zn2z znz;

    (* Comparison *)
    znz_compare     : znz -> znz -> comparison;
    znz_eq0         : znz -> bool;

    (* Basic arithmetic operations *)
    znz_opp_c       : znz -> carry znz;
    znz_opp         : znz -> znz;
    znz_opp_carry   : znz -> znz; (* the carry is known to be -1 *)

    znz_succ_c      : znz -> carry znz;
    znz_add_c       : znz -> znz -> carry znz;
    znz_add_carry_c : znz -> znz -> carry znz;
    znz_succ        : znz -> znz;
    znz_add         : znz -> znz -> znz;
    znz_add_carry   : znz -> znz -> znz;

    znz_pred_c      : znz -> carry znz;
    znz_sub_c       : znz -> znz -> carry znz;
    znz_sub_carry_c : znz -> znz -> carry znz;
    znz_pred        : znz -> znz;
    znz_sub         : znz -> znz -> znz;
    znz_sub_carry   : znz -> znz -> znz;

    znz_mul_c       : znz -> znz -> zn2z znz;
    znz_mul         : znz -> znz -> znz;
    znz_square_c    : znz -> zn2z znz;

    (* Special divisions operations *)
    znz_div21       : znz -> znz -> znz -> znz*znz;
    znz_div_gt      : znz -> znz -> znz * znz;
    znz_div         : znz -> znz -> znz * znz;

    znz_mod_gt      : znz -> znz -> znz; 
    znz_mod         : znz -> znz -> znz; 

    znz_gcd_gt      : znz -> znz -> znz;
    znz_gcd         : znz -> znz -> znz; 
    znz_add_mul_div : znz -> znz -> znz -> znz;
    znz_pos_mod     : znz -> znz -> znz;

   (* square root *)
    znz_is_even     : znz -> bool;
    znz_sqrt2       : znz -> znz -> znz * carry znz;
    znz_sqrt        : znz -> znz  }.

End ZnZ_Op.

Section Spec.
 Variable w : Set.
 Variable w_op : znz_op w.

 Let w_digits      := w_op.(znz_digits).
 Let w_zdigits     := w_op.(znz_zdigits).
 Let w_to_Z        := w_op.(znz_to_Z).
 Let w_of_pos      := w_op.(znz_of_pos).
 Let w_head0       := w_op.(znz_head0).
 Let w_tail0       := w_op.(znz_tail0).

 Let w0            := w_op.(znz_0).
 Let w1            := w_op.(znz_1).
 Let wBm1          := w_op.(znz_Bm1).

 Let wWW           := w_op.(znz_WW).
 Let w0W           := w_op.(znz_0W).
 Let wW0           := w_op.(znz_W0).

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

 Let w_pos_mod     := w_op.(znz_pos_mod).

 Let w_is_even     := w_op.(znz_is_even).
 Let w_sqrt2       := w_op.(znz_sqrt2).
 Let w_sqrt        := w_op.(znz_sqrt).

 Notation "[| x |]" := (w_to_Z x)  (at level 0, x at level 99).

 Let wB := base w_digits.

 Notation "[+| c |]" :=
   (interp_carry 1 wB w_to_Z c)  (at level 0, x at level 99).

 Notation "[-| c |]" :=
   (interp_carry (-1) wB w_to_Z c)  (at level 0, x at level 99).

 Notation "[|| x ||]" :=
   (zn2z_to_Z wB w_to_Z x)  (at level 0, x at level 99).
 
 Notation "[! n | x !]" := (gen_to_Z w_digits w_to_Z n x) 
       (at level 0, x at level 99).

 Record znz_spec : Set := mk_znz_spec {

    (* Conversion functions with Z *)
    spec_to_Z   : forall x, 0 <= [| x |] < wB;
    spec_of_pos : forall p,
           Zpos p = (Z_of_N (fst (w_of_pos p)))*wB + [|(snd (w_of_pos p))|];
    spec_zdigits : [| w_zdigits |] = Zpos w_digits;
    spec_more_than_1_digit: 1 < Zpos w_digits;

    (* Basic constructors *)
    spec_0   : [|w0|] = 0;
    spec_1   : [|w1|] = 1;
    spec_Bm1 : [|wBm1|] = wB - 1;
    spec_WW  : forall h l, [||wWW h l||] = [|h|] * wB + [|l|];
    spec_0W  : forall l, [||w0W l||] = [|l|];
    spec_W0  : forall h, [||wW0 h||] = [|h|]*wB;

    (* Comparison *)
    spec_compare :
     forall x y,
       match w_compare x y with
       | Eq => [|x|] = [|y|]
       | Lt => [|x|] < [|y|]
       | Gt => [|x|] > [|y|]
       end;
    spec_eq0 : forall x, w_eq0 x = true -> [|x|] = 0;
    (* Basic arithmetic operations *)
    spec_opp_c : forall x, [-|w_opp_c x|] = -[|x|];
    spec_opp : forall x, [|w_opp x|] = (-[|x|]) mod wB;
    spec_opp_carry : forall x, [|w_opp_carry x|] = wB - [|x|] - 1;

    spec_succ_c : forall x, [+|w_succ_c x|] = [|x|] + 1;
    spec_add_c  : forall x y, [+|w_add_c x y|] = [|x|] + [|y|];
    spec_add_carry_c : forall x y, [+|w_add_carry_c x y|] = [|x|] + [|y|] + 1;
    spec_succ : forall x, [|w_succ x|] = ([|x|] + 1) mod wB;
    spec_add : forall x y, [|w_add x y|] = ([|x|] + [|y|]) mod wB;
    spec_add_carry :
	 forall x y, [|w_add_carry x y|] = ([|x|] + [|y|] + 1) mod wB;

    spec_pred_c : forall x, [-|w_pred_c x|] = [|x|] - 1;
    spec_sub_c : forall x y, [-|w_sub_c x y|] = [|x|] - [|y|];
    spec_sub_carry_c : forall x y, [-|w_sub_carry_c x y|] = [|x|] - [|y|] - 1;
    spec_pred : forall x, [|w_pred x|] = ([|x|] - 1) mod wB;
    spec_sub : forall x y, [|w_sub x y|] = ([|x|] - [|y|]) mod wB;
    spec_sub_carry :
	 forall x y, [|w_sub_carry x y|] = ([|x|] - [|y|] - 1) mod wB;

    spec_mul_c : forall x y, [|| w_mul_c x y ||] = [|x|] * [|y|];
    spec_mul : forall x y, [|w_mul x y|] = ([|x|] * [|y|]) mod wB;
    spec_square_c : forall x, [|| w_square_c x||] = [|x|] * [|x|];

    (* Special divisions operations *)
    spec_div21 : forall a1 a2 b,
      wB/2 <= [|b|] ->
      [|a1|] < [|b|] ->
      let (q,r) := w_div21 a1 a2 b in
      [|a1|] *wB+ [|a2|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|];
    spec_div_gt : forall a b, [|a|] > [|b|] -> 0 < [|b|] ->
      let (q,r) := w_div_gt a b in
      [|a|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|];
    spec_div : forall a b, 0 < [|b|] ->
      let (q,r) := w_div a b in
      [|a|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|]; 
   
    spec_mod_gt : forall a b, [|a|] > [|b|] -> 0 < [|b|] ->
      [|w_mod_gt a b|] = [|a|] mod [|b|];
    spec_mod :  forall a b, 0 < [|b|] ->
      [|w_mod a b|] = [|a|] mod [|b|];
      
    spec_gcd_gt : forall a b, [|a|] > [|b|] ->
      Zis_gcd [|a|] [|b|] [|w_gcd_gt a b|];
    spec_gcd : forall a b, Zis_gcd [|a|] [|b|] [|w_gcd a b|];

 
    (* shift operations *)
    spec_head00:  forall x, [|x|] = 0 -> [|w_head0 x|] = Zpos w_digits;
    spec_head0  : forall x,  0 < [|x|] ->
	 wB/ 2 <= 2 ^ ([|w_head0 x|]) * [|x|] < wB;  
    spec_tail00:  forall x, [|x|] = 0 -> [|w_tail0 x|] = Zpos w_digits;
    spec_tail0  : forall x, 0 < [|x|] -> 
         exists y, 0 <= y /\ [|x|] = (2 * y + 1) * (2 ^ [|w_tail0 x|]) ;  
    spec_add_mul_div : forall x y p,
       [|p|] <= Zpos w_digits ->
       [| w_add_mul_div p x y |] =
         ([|x|] * (2 ^ [|p|]) +
          [|y|] / (2 ^ ((Zpos w_digits) - [|p|]))) mod wB;
    spec_pos_mod : forall w p,
       [|w_pos_mod p w|] = [|w|] mod (2 ^ [|p|]);
    (* sqrt *)
    spec_is_even : forall x,
      if w_is_even x then [|x|] mod 2 = 0 else [|x|] mod 2 = 1;
    spec_sqrt2 : forall x y,
       wB/ 4 <= [|x|] ->
       let (s,r) := w_sqrt2 x y in
          [||WW x y||] = [|s|] ^ 2 + [+|r|] /\
          [+|r|] <= 2 * [|s|];
    spec_sqrt : forall x,
       [|w_sqrt x|] ^ 2 <= [|x|] < ([|w_sqrt x|] + 1) ^ 2
  }.

End Spec.


Section znz_of_pos.
 
 Variable w : Set.
 Variable w_op : znz_op w.
 Variable op_spec : znz_spec w_op.

 Notation "[| x |]" := (znz_to_Z w_op x)  (at level 0, x at level 99).

 Definition znz_of_Z (w:Set) (op:znz_op w) z :=
 match z with
 | Zpos p => snd (op.(znz_of_pos) p)
 | _ => op.(znz_0)
 end.

 Theorem znz_of_pos_correct:
   forall p, Zpos p < base (znz_digits w_op) -> [|(snd (znz_of_pos w_op p))|] = Zpos p.
 intros p Hp.
 generalize (spec_of_pos op_spec p).
 case (znz_of_pos w_op p); intros n w1; simpl.
 case n; simpl Npos; auto with zarith.
 intros p1 Hp1; contradict Hp; apply Zle_not_lt.
 rewrite Hp1; auto with zarith.
 match goal with |- _ <= ?X + ?Y =>
  apply Zle_trans with X; auto with zarith
 end.
 match goal with |- ?X <= _ =>
  pattern X at 1; rewrite <- (Zmult_1_l); 
  apply Zmult_le_compat_r; auto with zarith
 end.
 case p1; simpl; intros; red; simpl; intros; discriminate.
 unfold base; auto with zarith.
 case (spec_to_Z op_spec w1); auto with zarith.
 Qed.

 Theorem znz_of_Z_correct:
   forall p, 0 <= p < base (znz_digits w_op) -> [|znz_of_Z w_op p|] = p.
 intros p; case p; simpl; try rewrite spec_0; auto.
 intros; rewrite znz_of_pos_correct; auto with zarith.
 intros p1 (H1, _); contradict H1; apply Zlt_not_le; red; simpl; auto.
 Qed.
End znz_of_pos.

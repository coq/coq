(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

(** * Signature and specification of a bounded integer structure *)

(** This file specifies how to represent [Z/nZ] when [n=2^d],
    [d] being the number of digits of these bounded integers. *)

Set Implicit Arguments.

Require Import ZArith.
Require Import Znumtheory.
Require Import Zpow_facts.
Require Import DoubleType.

Local Open Scope Z_scope.

(** First, a description via an operator record and a spec record. *)

Module ZnZ.

 Class Ops (t:Type) := MkOps {

    (* Conversion functions with Z *)
    digits : positive;
    zdigits: t;
    to_Z   : t -> Z;
    of_pos : positive -> N * t; (* Euclidean division by [2^digits] *)
    head0  : t -> t; (* number of digits 0 in front of the number *)
    tail0  : t -> t; (* number of digits 0 at the bottom of the number *)

    (* Basic numbers *)
    zero : t;
    one  : t;
    minus_one : t;  (* [2^digits-1], which is equivalent to [-1] *)

    (* Comparison *)
    compare     : t -> t -> comparison;
    eq0         : t -> bool;

    (* Basic arithmetic operations *)
    opp_c       : t -> carry t;
    opp         : t -> t;
    opp_carry   : t -> t; (* the carry is known to be -1 *)

    succ_c      : t -> carry t;
    add_c       : t -> t -> carry t;
    add_carry_c : t -> t -> carry t;
    succ        : t -> t;
    add         : t -> t -> t;
    add_carry   : t -> t -> t;

    pred_c      : t -> carry t;
    sub_c       : t -> t -> carry t;
    sub_carry_c : t -> t -> carry t;
    pred        : t -> t;
    sub         : t -> t -> t;
    sub_carry   : t -> t -> t;

    mul_c       : t -> t -> zn2z t;
    mul         : t -> t -> t;
    square_c    : t -> zn2z t;

    (* Special divisions operations *)
    div21       : t -> t -> t -> t*t;
    div_gt      : t -> t -> t * t; (* specialized version of [div] *)
    div         : t -> t -> t * t;

    modulo_gt   : t -> t -> t; (* specialized version of [mod] *)
    modulo      : t -> t -> t;

    gcd_gt      : t -> t -> t; (* specialized version of [gcd] *)
    gcd         : t -> t -> t;
    (* [add_mul_div p i j] is a combination of the [(digits-p)]
       low bits of [i] above the [p] high bits of [j]:
       [add_mul_div p i j = i*2^p+j/2^(digits-p)] *)
    add_mul_div : t -> t -> t -> t;
    (* [pos_mod p i] is [i mod 2^p] *)
    pos_mod     : t -> t -> t;

    is_even     : t -> bool;
    (* square root *)
    sqrt2       : t -> t -> t * carry t;
    sqrt        : t -> t;
    (* bitwise operations *)
    lor         : t -> t -> t;
    land        : t -> t -> t;
    lxor        : t -> t -> t }.
 
 Section Specs.
 Context {t : Type}{ops : Ops t}.

 Notation "[| x |]" := (to_Z x)  (at level 0, x at level 99).

 Let wB := base digits.

 Notation "[+| c |]" :=
   (interp_carry 1 wB to_Z c)  (at level 0, c at level 99).

 Notation "[-| c |]" :=
   (interp_carry (-1) wB to_Z c)  (at level 0, c at level 99).

 Notation "[|| x ||]" :=
   (zn2z_to_Z wB to_Z x)  (at level 0, x at level 99).

 Class Specs := MkSpecs {

    (* Conversion functions with Z *)
    spec_to_Z   : forall x, 0 <= [| x |] < wB;
    spec_of_pos : forall p,
           Zpos p = (Z.of_N (fst (of_pos p)))*wB + [|(snd (of_pos p))|];
    spec_zdigits : [| zdigits |] = Zpos digits;
    spec_more_than_1_digit: 1 < Zpos digits;

    (* Basic numbers *)
    spec_0   : [|zero|] = 0;
    spec_1   : [|one|] = 1;
    spec_m1 : [|minus_one|] = wB - 1;

    (* Comparison *)
    spec_compare : forall x y, compare x y = ([|x|] ?= [|y|]);
    (* NB: the spec of [eq0] is deliberately partial,
       see DoubleCyclic where [eq0 x = true <-> x = W0] *)
    spec_eq0 : forall x, eq0 x = true -> [|x|] = 0;
    (* Basic arithmetic operations *)
    spec_opp_c : forall x, [-|opp_c x|] = -[|x|];
    spec_opp : forall x, [|opp x|] = (-[|x|]) mod wB;
    spec_opp_carry : forall x, [|opp_carry x|] = wB - [|x|] - 1;

    spec_succ_c : forall x, [+|succ_c x|] = [|x|] + 1;
    spec_add_c  : forall x y, [+|add_c x y|] = [|x|] + [|y|];
    spec_add_carry_c : forall x y, [+|add_carry_c x y|] = [|x|] + [|y|] + 1;
    spec_succ : forall x, [|succ x|] = ([|x|] + 1) mod wB;
    spec_add : forall x y, [|add x y|] = ([|x|] + [|y|]) mod wB;
    spec_add_carry :
	 forall x y, [|add_carry x y|] = ([|x|] + [|y|] + 1) mod wB;

    spec_pred_c : forall x, [-|pred_c x|] = [|x|] - 1;
    spec_sub_c : forall x y, [-|sub_c x y|] = [|x|] - [|y|];
    spec_sub_carry_c : forall x y, [-|sub_carry_c x y|] = [|x|] - [|y|] - 1;
    spec_pred : forall x, [|pred x|] = ([|x|] - 1) mod wB;
    spec_sub : forall x y, [|sub x y|] = ([|x|] - [|y|]) mod wB;
    spec_sub_carry :
	 forall x y, [|sub_carry x y|] = ([|x|] - [|y|] - 1) mod wB;

    spec_mul_c : forall x y, [|| mul_c x y ||] = [|x|] * [|y|];
    spec_mul : forall x y, [|mul x y|] = ([|x|] * [|y|]) mod wB;
    spec_square_c : forall x, [|| square_c x||] = [|x|] * [|x|];

    (* Special divisions operations *)
    spec_div21 : forall a1 a2 b,
      wB/2 <= [|b|] ->
      [|a1|] < [|b|] ->
      let (q,r) := div21 a1 a2 b in
      [|a1|] *wB+ [|a2|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|];
    spec_div_gt : forall a b, [|a|] > [|b|] -> 0 < [|b|] ->
      let (q,r) := div_gt a b in
      [|a|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|];
    spec_div : forall a b, 0 < [|b|] ->
      let (q,r) := div a b in
      [|a|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|];

    spec_modulo_gt : forall a b, [|a|] > [|b|] -> 0 < [|b|] ->
      [|modulo_gt a b|] = [|a|] mod [|b|];
    spec_modulo :  forall a b, 0 < [|b|] ->
      [|modulo a b|] = [|a|] mod [|b|];

    spec_gcd_gt : forall a b, [|a|] > [|b|] ->
      Zis_gcd [|a|] [|b|] [|gcd_gt a b|];
    spec_gcd : forall a b, Zis_gcd [|a|] [|b|] [|gcd a b|];


    (* shift operations *)
    spec_head00:  forall x, [|x|] = 0 -> [|head0 x|] = Zpos digits;
    spec_head0  : forall x,  0 < [|x|] ->
	 wB/ 2 <= 2 ^ ([|head0 x|]) * [|x|] < wB;
    spec_tail00:  forall x, [|x|] = 0 -> [|tail0 x|] = Zpos digits;
    spec_tail0  : forall x, 0 < [|x|] ->
         exists y, 0 <= y /\ [|x|] = (2 * y + 1) * (2 ^ [|tail0 x|]) ;
    spec_add_mul_div : forall x y p,
       [|p|] <= Zpos digits ->
       [| add_mul_div p x y |] =
         ([|x|] * (2 ^ [|p|]) +
          [|y|] / (2 ^ ((Zpos digits) - [|p|]))) mod wB;
    spec_pos_mod : forall w p,
       [|pos_mod p w|] = [|w|] mod (2 ^ [|p|]);
    (* sqrt *)
    spec_is_even : forall x,
      if is_even x then [|x|] mod 2 = 0 else [|x|] mod 2 = 1;
    spec_sqrt2 : forall x y,
       wB/ 4 <= [|x|] ->
       let (s,r) := sqrt2 x y in
          [||WW x y||] = [|s|] ^ 2 + [+|r|] /\
          [+|r|] <= 2 * [|s|];
    spec_sqrt : forall x,
       [|sqrt x|] ^ 2 <= [|x|] < ([|sqrt x|] + 1) ^ 2;
    spec_lor : forall x y, [|lor x y|] = Z.lor [|x|] [|y|];
    spec_land : forall x y, [|land x y|] = Z.land [|x|] [|y|];
    spec_lxor : forall x y, [|lxor x y|] = Z.lxor [|x|] [|y|]
  }.

 End Specs.

 Arguments Specs {t} ops.

 (** Generic construction of double words *)

 Section WW.

 Context {t : Type}{ops : Ops t}{specs : Specs ops}.

 Let wB := base digits.

 Definition WO' (eq0:t->bool) zero h :=
  if eq0 h then W0 else WW h zero.

 Definition WO := Eval lazy beta delta [WO'] in
   let eq0 := ZnZ.eq0 in
   let zero := ZnZ.zero in
   WO' eq0 zero.

 Definition OW' (eq0:t->bool) zero l :=
  if eq0 l then W0 else WW zero l.

 Definition OW := Eval lazy beta delta [OW'] in
   let eq0 := ZnZ.eq0 in
   let zero := ZnZ.zero in
   OW' eq0 zero.

 Definition WW'  (eq0:t->bool) zero h l :=
  if eq0 h then OW' eq0 zero l else WW h l.

 Definition WW := Eval lazy beta delta [WW' OW'] in
   let eq0 := ZnZ.eq0 in
   let zero := ZnZ.zero in
   WW' eq0 zero.

 Lemma spec_WO : forall h,
   zn2z_to_Z wB to_Z (WO h) = (to_Z h)*wB.
 Proof.
 unfold zn2z_to_Z, WO; simpl; intros.
 case_eq (eq0 h); intros.
 rewrite (spec_eq0 _ H); auto.
 rewrite spec_0; auto with zarith.
 Qed.

 Lemma spec_OW : forall l,
   zn2z_to_Z wB to_Z (OW l) = to_Z l.
 Proof.
 unfold zn2z_to_Z, OW; simpl; intros.
 case_eq (eq0 l); intros.
 rewrite (spec_eq0 _ H); auto.
 rewrite spec_0; auto with zarith.
 Qed.

 Lemma spec_WW : forall h l,
  zn2z_to_Z wB to_Z (WW h l) = (to_Z h)*wB + to_Z l.
 Proof.
 unfold WW; simpl; intros.
 case_eq (eq0 h); intros.
 rewrite (spec_eq0 _ H); auto.
 fold (OW l).
 rewrite spec_OW; auto.
 simpl; auto.
 Qed.

 End WW.

 (** Injecting [Z] numbers into a cyclic structure *)

 Section Of_Z.

 Context {t : Type}{ops : Ops t}{specs : Specs ops}.

 Notation "[| x |]" := (to_Z x)  (at level 0, x at level 99).

 Theorem of_pos_correct:
   forall p, Zpos p < base digits -> [|(snd (of_pos p))|] = Zpos p.
 Proof.
 intros p Hp.
 generalize (spec_of_pos p).
 case (of_pos p); intros n w1; simpl.
 case n; auto with zarith.
 intros p1 Hp1; contradict Hp; apply Z.le_ngt.
 replace (base digits) with (1 * base digits + 0) by ring.
 rewrite Hp1.
 apply Z.add_le_mono.
 apply Z.mul_le_mono_nonneg; auto with zarith.
 case p1; simpl; intros; red; simpl; intros; discriminate.
 unfold base; auto with zarith.
 case (spec_to_Z w1); auto with zarith.
 Qed.

 Definition of_Z z :=
 match z with
 | Zpos p => snd (of_pos p)
 | _ => zero
 end.

 Theorem of_Z_correct:
   forall p, 0 <= p < base digits -> [|of_Z p|] = p.
 Proof.
 intros p; case p; simpl; try rewrite spec_0; auto.
 intros; rewrite of_pos_correct; auto with zarith.
 intros p1 (H1, _); contradict H1; apply Z.lt_nge; red; simpl; auto.
 Qed.

 End Of_Z.

End ZnZ.

(** A modular specification grouping the earlier records. *)

Module Type CyclicType.
 Parameter t : Type.
 Declare Instance ops : ZnZ.Ops t.
 Declare Instance specs : ZnZ.Specs ops.
End CyclicType.


(** A Cyclic structure can be seen as a ring *)

Module CyclicRing (Import Cyclic : CyclicType).

Local Notation "[| x |]" := (ZnZ.to_Z x) (at level 0, x at level 99).

Definition eq (n m : t) := [| n |] = [| m |].

Local Infix "=="  := eq (at level 70).
Local Notation "0" := ZnZ.zero.
Local Notation "1" := ZnZ.one.
Local Infix "+" := ZnZ.add.
Local Infix "-" := ZnZ.sub.
Local Notation "- x" := (ZnZ.opp x).
Local Infix "*" := ZnZ.mul.
Local Notation wB := (base ZnZ.digits).

Hint Rewrite ZnZ.spec_0 ZnZ.spec_1 ZnZ.spec_add ZnZ.spec_mul
 ZnZ.spec_opp ZnZ.spec_sub
 : cyclic.

Ltac zify := unfold eq in *; autorewrite with cyclic.

Lemma add_0_l : forall x, 0 + x == x.
Proof.
intros. zify. rewrite Z.add_0_l.
apply Zmod_small. apply ZnZ.spec_to_Z.
Qed.

Lemma add_comm : forall x y, x + y == y + x.
Proof.
intros. zify. now rewrite Z.add_comm.
Qed.

Lemma add_assoc : forall x y z, x + (y + z) == x + y + z.
Proof.
intros. zify. now rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_l, Z.add_assoc.
Qed.

Lemma mul_1_l : forall x, 1 * x == x.
Proof.
intros. zify. rewrite Z.mul_1_l.
apply Zmod_small. apply ZnZ.spec_to_Z.
Qed.

Lemma mul_comm : forall x y, x * y == y * x.
Proof.
intros. zify. now rewrite Z.mul_comm.
Qed.

Lemma mul_assoc : forall x y z, x * (y * z) == x * y * z.
Proof.
intros. zify. now rewrite Zmult_mod_idemp_r, Zmult_mod_idemp_l, Z.mul_assoc.
Qed.

Lemma mul_add_distr_r : forall x y z, (x+y)*z == x*z + y*z.
Proof.
intros. zify. now rewrite <- Zplus_mod, Zmult_mod_idemp_l, Z.mul_add_distr_r.
Qed.

Lemma add_opp_r : forall x y, x + - y == x-y.
Proof.
intros. zify. rewrite <- Zminus_mod_idemp_r. unfold Z.sub.
destruct (Z.eq_dec ([|y|] mod wB) 0) as [EQ|NEQ].
rewrite Z_mod_zero_opp_full, EQ, 2 Z.add_0_r; auto.
rewrite Z_mod_nz_opp_full by auto.
rewrite <- Zplus_mod_idemp_r, <- Zminus_mod_idemp_l.
rewrite Z_mod_same_full. simpl. now rewrite Zplus_mod_idemp_r.
Qed.

Lemma add_opp_diag_r : forall x, x + - x == 0.
Proof.
intros. red. rewrite add_opp_r. zify. now rewrite Z.sub_diag, Zmod_0_l.
Qed.

Lemma CyclicRing : ring_theory 0 1 ZnZ.add ZnZ.mul ZnZ.sub ZnZ.opp eq.
Proof.
constructor.
exact add_0_l. exact add_comm. exact add_assoc.
exact mul_1_l. exact mul_comm. exact mul_assoc.
exact mul_add_distr_r.
symmetry. apply add_opp_r.
exact add_opp_diag_r.
Qed.

Definition eqb x y :=
 match ZnZ.compare x y with Eq => true | _ => false end.

Lemma eqb_eq : forall x y, eqb x y = true <-> x == y.
Proof.
 intros. unfold eqb, eq.
 rewrite ZnZ.spec_compare.
 case Z.compare_spec; intuition; try discriminate.
Qed.

Lemma eqb_correct : forall x y, eqb x y = true -> x==y.
Proof. now apply eqb_eq. Qed.

End CyclicRing.

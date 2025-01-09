(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Instances of [ZifyClasses] for emulating the existing zify.
   Each instance is registered using a Add 'class' 'name_of_instance'.
 *)

Require Import Arith BinInt BinNat Zeven Znat Nnat.
Require Import ZifyClasses.
Declare ML Module "rocq-runtime.plugins.zify".
Local Open Scope Z_scope.

Ltac refl :=
  abstract (intros ; match goal with
                     | |- context[@inj _ _ ?X] => unfold X, inj
                     end ; reflexivity).


#[global]
Instance Inj_Z_Z : InjTyp Z Z :=
  mkinj _ _ (fun x => x) (fun x =>  True ) (fun _ => I).
Add Zify InjTyp Inj_Z_Z.

(** Support for nat *)

#[global]
Instance Inj_nat_Z : InjTyp nat Z :=
  mkinj _ _ Z.of_nat (fun x =>  0 <= x ) Nat2Z.is_nonneg.
Add Zify InjTyp Inj_nat_Z.

(* zify_nat_rel *)
#[global]
Instance Op_ge : BinRel ge :=
  { TR := Z.ge; TRInj := Nat2Z.inj_ge }.
Add Zify BinRel Op_ge.

#[global]
Instance Op_lt : BinRel lt :=
  { TR := Z.lt; TRInj := Nat2Z.inj_lt }.
Add Zify BinRel Op_lt.

#[global]
Instance Op_Nat_lt : BinRel Nat.lt := Op_lt.
Add Zify BinRel Op_Nat_lt.

#[global]
Instance Op_gt : BinRel gt :=
  { TR := Z.gt; TRInj := Nat2Z.inj_gt }.
Add Zify BinRel Op_gt.

#[global]
Instance Op_le : BinRel le :=
  { TR := Z.le; TRInj := Nat2Z.inj_le }.
Add Zify BinRel Op_le.

#[global]
Instance Op_Nat_le : BinRel Nat.le := Op_le.
Add Zify BinRel Op_Nat_le.

#[global]
Instance Op_eq_nat : BinRel (@eq nat) :=
  { TR := @eq Z ; TRInj x y := iff_sym (Nat2Z.inj_iff x y) }.
Add Zify BinRel Op_eq_nat.

#[global]
Instance Op_Nat_eq : BinRel (Nat.eq) := Op_eq_nat.
Add Zify BinRel Op_Nat_eq.

(* zify_nat_op *)
#[global]
Instance Op_plus : BinOp Nat.add :=
  { TBOp := Z.add; TBOpInj := Nat2Z.inj_add }.
Add Zify BinOp Op_plus.

#[global]
Instance Op_sub : BinOp Nat.sub :=
  { TBOp n m := Z.max 0 (n - m) ; TBOpInj := Nat2Z.inj_sub_max }.
Add Zify BinOp Op_sub.

#[global]
Instance Op_mul : BinOp Nat.mul :=
  { TBOp := Z.mul ; TBOpInj := Nat2Z.inj_mul }.
Add Zify BinOp Op_mul.

#[global]
Instance Op_min : BinOp Nat.min :=
  { TBOp := Z.min ; TBOpInj := Nat2Z.inj_min }.
Add Zify BinOp Op_min.

#[global]
Instance Op_max : BinOp Nat.max :=
  { TBOp := Z.max ; TBOpInj := Nat2Z.inj_max }.
Add Zify BinOp Op_max.

#[global]
Instance Op_pred : UnOp Nat.pred :=
  { TUOp n := Z.max 0 (n - 1) ; TUOpInj := Nat2Z.inj_pred_max }.
Add Zify UnOp Op_pred.

#[global]
Instance Op_S : UnOp S :=
  { TUOp x := Z.add x 1 ; TUOpInj := Nat2Z.inj_succ }.
Add Zify UnOp Op_S.

#[global]
Instance Op_O : CstOp O :=
  { TCst := Z0 ; TCstInj := eq_refl (Z.of_nat 0) }.
Add Zify CstOp Op_O.

#[global]
Instance Op_Z_abs_nat : UnOp  Z.abs_nat :=
  { TUOp := Z.abs ; TUOpInj := Zabs2Nat.id_abs }.
Add Zify UnOp Op_Z_abs_nat.

#[global]
Instance Op_nat_div2 : UnOp Nat.div2 :=
  { TUOp x := x / 2 ;
    TUOpInj x := ltac:(now rewrite Nat2Z.inj_div2, Z.div2_div) }.
Add Zify UnOp Op_nat_div2.

#[global]
Instance Op_nat_double : UnOp Nat.double :=
  {| TUOp := Z.mul 2 ; TUOpInj := Nat2Z.inj_double |}.
Add Zify UnOp Op_nat_double.

(** Support for positive *)

#[global]
Instance Inj_pos_Z : InjTyp positive Z :=
  { inj := Zpos ; pred x := 0 < x ; cstr := Pos2Z.pos_is_pos }.
Add Zify InjTyp Inj_pos_Z.

#[global]
Instance Op_pos_to_nat : UnOp  Pos.to_nat :=
  {TUOp x := x ; TUOpInj := positive_nat_Z}.
Add Zify UnOp Op_pos_to_nat.

#[global]
Instance Inj_N_Z : InjTyp N Z :=
  mkinj _ _ Z.of_N (fun x =>  0 <= x ) N2Z.is_nonneg.
Add Zify InjTyp Inj_N_Z.


#[global]
Instance Op_N_to_nat : UnOp  N.to_nat :=
  { TUOp x := x ; TUOpInj := N_nat_Z }.
Add Zify UnOp Op_N_to_nat.

(* zify_positive_rel *)

#[global]
Instance Op_pos_ge : BinRel Pos.ge :=
  { TR := Z.ge; TRInj x y := iff_refl (Z.pos x >= Z.pos y) }.
Add Zify BinRel Op_pos_ge.

#[global]
Instance Op_pos_lt : BinRel Pos.lt :=
  { TR := Z.lt; TRInj x y := iff_refl (Z.pos x < Z.pos y) }.
Add Zify BinRel Op_pos_lt.

#[global]
Instance Op_pos_gt : BinRel Pos.gt :=
  { TR := Z.gt; TRInj x y := iff_refl (Z.pos x > Z.pos y) }.
Add Zify BinRel Op_pos_gt.

#[global]
Instance Op_pos_le : BinRel Pos.le :=
  { TR := Z.le; TRInj x y := iff_refl (Z.pos x <= Z.pos y) }.
Add Zify BinRel Op_pos_le.

Lemma eq_pos_inj x y : x = y <-> Z.pos x = Z.pos y.
Proof.
  apply (iff_sym (Pos2Z.inj_iff x y)).
Qed.

#[global]
Instance Op_eq_pos : BinRel (@eq positive) :=
  { TR := @eq Z ; TRInj := eq_pos_inj }.
Add Zify BinRel Op_eq_pos.

(* zify_positive_op *)

#[global]
Instance Op_Z_of_N : UnOp Z.of_N :=
  { TUOp x := x ; TUOpInj x := eq_refl (Z.of_N x) }.
Add Zify UnOp Op_Z_of_N.

#[global]
Instance Op_Z_to_N : UnOp Z.to_N :=
  { TUOp x := Z.max 0 x ; TUOpInj x := ltac:(now destruct x) }.
Add Zify UnOp Op_Z_to_N.

#[global]
Instance Op_Z_neg : UnOp Z.neg :=
  { TUOp := Z.opp ; TUOpInj x := eq_refl (Zneg x) }.
Add Zify UnOp Op_Z_neg.

#[global]
Instance Op_Z_pos : UnOp Z.pos :=
  { TUOp x := x ; TUOpInj x := eq_refl (Z.pos x) }.
Add Zify UnOp Op_Z_pos.

#[global]
Instance Op_pos_succ : UnOp Pos.succ :=
  { TUOp x := x + 1 ; TUOpInj := Pos2Z.inj_succ }.
Add Zify UnOp Op_pos_succ.

#[global]
Instance Op_pos_pred_double : UnOp Pos.pred_double :=
{ TUOp x := 2 * x - 1 ; TUOpInj _ := eq_refl }.
Add Zify UnOp Op_pos_pred_double.

#[global]
Instance Op_pos_pred : UnOp Pos.pred :=
  { TUOp x := Z.max 1 (x - 1) ;
    TUOpInj x := ltac:(rewrite <- Pos.sub_1_r; apply Pos2Z.inj_sub_max) }.
Add Zify UnOp Op_pos_pred.

#[global]
Instance Op_pos_predN : UnOp Pos.pred_N :=
  { TUOp x := x - 1 ;
    TUOpInj x := ltac: (now destruct x; rewrite N.pos_pred_spec) }.
Add Zify UnOp Op_pos_predN.

#[global]
Instance Op_pos_of_succ_nat : UnOp Pos.of_succ_nat :=
  { TUOp x := x + 1 ; TUOpInj := Zpos_P_of_succ_nat }.
Add Zify UnOp Op_pos_of_succ_nat.

#[global]
Instance Op_pos_of_nat : UnOp Pos.of_nat :=
  { TUOp x := Z.max 1 x ;
    TUOpInj x := ltac: (now destruct x;
                        [|rewrite <- Pos.of_nat_succ, <- (Nat2Z.inj_max 1)]) }.
Add Zify UnOp Op_pos_of_nat.

#[global]
Instance Op_pos_add : BinOp Pos.add :=
  { TBOp := Z.add ; TBOpInj _ _ := eq_refl }.
Add Zify BinOp Op_pos_add.

#[global]
Instance Op_pos_add_carry : BinOp Pos.add_carry :=
  { TBOp x y := x + y + 1 ;
    TBOpInj := ltac:(now intros; rewrite Pos.add_carry_spec, Pos2Z.inj_succ) }.
Add Zify BinOp Op_pos_add_carry.

#[global]
Instance Op_pos_sub : BinOp Pos.sub :=
  { TBOp n m := Z.max 1 (n - m) ; TBOpInj := Pos2Z.inj_sub_max }.
Add Zify BinOp Op_pos_sub.

#[global]
Instance Op_pos_mul : BinOp Pos.mul :=
  { TBOp := Z.mul ; TBOpInj _ _ := eq_refl }.
Add Zify BinOp Op_pos_mul.

#[global]
Instance Op_pos_min : BinOp Pos.min :=
  { TBOp := Z.min ; TBOpInj := Pos2Z.inj_min }.
Add Zify BinOp Op_pos_min.

#[global]
Instance Op_pos_max : BinOp Pos.max :=
  { TBOp := Z.max ; TBOpInj := Pos2Z.inj_max }.
Add Zify BinOp Op_pos_max.

#[global]
Instance Op_pos_pow : BinOp Pos.pow :=
  { TBOp := Z.pow ; TBOpInj := Pos2Z.inj_pow }.
Add Zify BinOp Op_pos_pow.

#[global]
Instance Op_pos_square : UnOp Pos.square :=
  { TUOp := Z.square ; TUOpInj := Pos2Z.inj_square }.
Add Zify UnOp Op_pos_square.

#[global]
Instance Op_Pos_Nsucc_double : UnOp Pos.Nsucc_double :=
  { TUOp x := 2 * x + 1 ; TUOpInj x := ltac:(now destruct x) }.
Add Zify UnOp Op_Pos_Nsucc_double.

#[global]
Instance Op_Pos_Ndouble : UnOp Pos.Ndouble :=
  { TUOp x := 2 * x ; TUOpInj x := ltac:(now destruct x) }.
Add Zify UnOp Op_Pos_Ndouble.

#[global]
Instance Op_xO : UnOp xO :=
  { TUOp x := 2 * x ; TUOpInj _ := eq_refl }.
Add Zify UnOp Op_xO.

#[global]
Instance Op_xI : UnOp xI :=
  { TUOp x := 2 * x + 1 ; TUOpInj _ := eq_refl }.
Add Zify UnOp Op_xI.

#[global]
Instance Op_xH : CstOp xH :=
  { TCst := 1%Z ; TCstInj := eq_refl }.
Add Zify CstOp Op_xH.

#[global]
Instance Op_Z_of_nat : UnOp Z.of_nat:=
  { TUOp x := x ; TUOpInj x := eq_refl (Z.of_nat x) }.
Add Zify UnOp Op_Z_of_nat.

(* zify_N_rel *)
#[global]
Instance Op_N_ge : BinRel N.ge :=
  { TR := Z.ge ; TRInj := N2Z.inj_ge }.
Add Zify BinRel Op_N_ge.

#[global]
Instance Op_N_lt : BinRel N.lt :=
  { TR := Z.lt ; TRInj := N2Z.inj_lt }.
Add Zify BinRel Op_N_lt.

#[global]
Instance Op_N_gt : BinRel N.gt :=
  { TR := Z.gt ; TRInj := N2Z.inj_gt }.
Add Zify BinRel Op_N_gt.

#[global]
Instance Op_N_le : BinRel N.le :=
  { TR := Z.le ; TRInj := N2Z.inj_le }.
Add Zify BinRel Op_N_le.

#[global]
Instance Op_eq_N : BinRel (@eq N) :=
  { TR := @eq Z ; TRInj x y := iff_sym (N2Z.inj_iff x y) }.
Add Zify BinRel Op_eq_N.

(* zify_N_op *)
#[global]
Instance Op_N_N0 : CstOp  N0 :=
  { TCst := Z0 ; TCstInj := eq_refl }.
Add Zify CstOp Op_N_N0.

#[global]
Instance Op_N_Npos : UnOp  Npos :=
  { TUOp x := x ; TUOpInj _ := eq_refl }.
Add Zify UnOp Op_N_Npos.

#[global]
Instance Op_N_of_nat : UnOp  N.of_nat :=
  { TUOp x := x ; TUOpInj := nat_N_Z }.
Add Zify UnOp Op_N_of_nat.

#[global]
Instance Op_Z_abs_N : UnOp Z.abs_N :=
  { TUOp := Z.abs ; TUOpInj := N2Z.inj_abs_N }.
Add Zify UnOp Op_Z_abs_N.

#[global]
Instance Op_N_pos : UnOp N.pos :=
  { TUOp x := x ; TUOpInj _ := eq_refl }.
Add Zify UnOp Op_N_pos.

#[global]
Instance Op_N_add : BinOp N.add :=
  { TBOp := Z.add ; TBOpInj := N2Z.inj_add }.
Add Zify BinOp Op_N_add.

#[global]
Instance Op_N_min : BinOp N.min :=
  { TBOp := Z.min ; TBOpInj := N2Z.inj_min }.
Add Zify BinOp Op_N_min.

#[global]
Instance Op_N_max : BinOp N.max :=
  { TBOp := Z.max ; TBOpInj := N2Z.inj_max }.
Add Zify BinOp Op_N_max.

#[global]
Instance Op_N_mul : BinOp N.mul :=
  { TBOp := Z.mul ; TBOpInj := N2Z.inj_mul }.
Add Zify BinOp Op_N_mul.

#[global]
Instance Op_N_sub : BinOp N.sub :=
  { TBOp x y := Z.max 0 (x - y) ; TBOpInj := N2Z.inj_sub_max }.
Add Zify BinOp Op_N_sub.

#[global]
Instance Op_N_div : BinOp N.div :=
  { TBOp := Z.div ; TBOpInj := N2Z.inj_div }.
Add Zify BinOp Op_N_div.

#[global]
Instance Op_N_mod : BinOp N.modulo :=
  { TBOp := Z.rem ; TBOpInj := N2Z.inj_rem }.
Add Zify BinOp Op_N_mod.

#[global]
Instance Op_N_pred : UnOp N.pred :=
  { TUOp x := Z.max 0 (x - 1) ;
    TUOpInj x := ltac:(rewrite N.pred_sub; apply N2Z.inj_sub_max) }.
Add Zify UnOp Op_N_pred.

#[global]
Instance Op_N_succ : UnOp N.succ :=
  { TUOp x := x + 1 ; TUOpInj := N2Z.inj_succ }.
Add Zify UnOp Op_N_succ.

#[global]
Instance Op_N_succ_double : UnOp N.succ_double :=
  { TUOp x := 2 * x + 1 ; TUOpInj x := ltac:(now destruct x) }.
Add Zify UnOp Op_N_succ_double.

#[global]
Instance Op_N_double : UnOp N.double :=
  { TUOp x := 2 * x ; TUOpInj x := ltac:(now destruct x) }.
Add Zify UnOp Op_N_double.

#[global]
Instance Op_N_succ_pos : UnOp N.succ_pos :=
  { TUOp x := x + 1 ;
    TUOpInj x := ltac:(now destruct x; simpl; [| rewrite Pplus_one_succ_r]) }.
Add Zify UnOp Op_N_succ_pos.

#[global]
Instance Op_N_div2 : UnOp N.div2 :=
  { TUOp x := x / 2 ;
    TUOpInj x := ltac:(now rewrite N2Z.inj_div2, Z.div2_div) }.
Add Zify UnOp Op_N_div2.

#[global]
Instance Op_N_pow : BinOp N.pow :=
  { TBOp := Z.pow ; TBOpInj := N2Z.inj_pow }.
Add Zify BinOp Op_N_pow.

#[global]
Instance Op_N_square : UnOp N.square :=
  { TUOp x := x * x ;
    TUOpInj x := ltac:(now rewrite N.square_spec, N2Z.inj_mul) }.
Add Zify UnOp Op_N_square.

(** Support for Z - injected to itself *)

(* zify_Z_rel *)
#[global]
Instance Op_Z_ge : BinRel Z.ge :=
  { TR := Z.ge ; TRInj x y := iff_refl (x>= y) }.
Add Zify BinRel Op_Z_ge.

#[global]
Instance Op_Z_lt : BinRel Z.lt :=
  { TR := Z.lt ; TRInj x y := iff_refl (x < y) }.
Add Zify BinRel Op_Z_lt.

#[global]
Instance Op_Z_gt : BinRel Z.gt :=
  { TR := Z.gt ;TRInj x y := iff_refl (x > y) }.
Add Zify BinRel Op_Z_gt.

#[global]
Instance Op_Z_le : BinRel Z.le :=
  { TR := Z.le ;TRInj x y := iff_refl (x <= y) }.
Add Zify BinRel Op_Z_le.

#[global]
Instance Op_eqZ : BinRel (@eq Z) :=
  { TR := @eq Z ; TRInj x y := iff_refl (x = y) }.
Add Zify BinRel Op_eqZ.

#[global]
Instance Op_Z_Z0 : CstOp Z0 :=
  { TCst := Z0  ; TCstInj := eq_refl }.
Add Zify CstOp Op_Z_Z0.

#[global]
Instance Op_Z_add : BinOp Z.add :=
  { TBOp := Z.add  ; TBOpInj _ _ := eq_refl }.
Add Zify BinOp Op_Z_add.

#[global]
Instance Op_Z_min : BinOp Z.min :=
  { TBOp := Z.min ; TBOpInj _ _ := eq_refl }.
Add Zify BinOp Op_Z_min.

#[global]
Instance Op_Z_max : BinOp Z.max :=
  { TBOp := Z.max ; TBOpInj _ _ := eq_refl }.
Add Zify BinOp Op_Z_max.

#[global]
Instance Op_Z_mul : BinOp Z.mul :=
  { TBOp := Z.mul ; TBOpInj _ _ := eq_refl }.
Add Zify BinOp Op_Z_mul.

#[global]
Instance Op_Z_sub : BinOp Z.sub :=
  { TBOp := Z.sub ; TBOpInj _ _ := eq_refl }.
Add Zify BinOp Op_Z_sub.

#[global]
Instance Op_Z_div : BinOp Z.div :=
  { TBOp := Z.div ; TBOpInj _ _ := eq_refl }.
Add Zify BinOp Op_Z_div.

#[global]
Instance Op_Z_mod : BinOp Z.modulo :=
  { TBOp := Z.modulo ; TBOpInj _ _ := eq_refl }.
Add Zify BinOp Op_Z_mod.

#[global]
Instance Op_Z_rem : BinOp Z.rem :=
  { TBOp := Z.rem ; TBOpInj _ _ := eq_refl }.
Add Zify BinOp Op_Z_rem.

#[global]
Instance Op_Z_quot : BinOp Z.quot :=
  { TBOp := Z.quot ; TBOpInj _ _ := eq_refl }.
Add Zify BinOp Op_Z_quot.

#[global]
Instance Op_Z_succ : UnOp Z.succ :=
  { TUOp x := x + 1 ; TUOpInj _ := eq_refl }.
Add Zify UnOp Op_Z_succ.

#[global]
Instance Op_Z_pred : UnOp Z.pred :=
  { TUOp x := x - 1 ; TUOpInj _ := eq_refl }.
Add Zify UnOp Op_Z_pred.

#[global]
Instance Op_Z_opp : UnOp Z.opp :=
  { TUOp := Z.opp ; TUOpInj _ := eq_refl }.
Add Zify UnOp Op_Z_opp.

#[global]
Instance Op_Z_abs : UnOp Z.abs :=
  { TUOp := Z.abs ; TUOpInj _ := eq_refl }.
Add Zify UnOp Op_Z_abs.

#[global]
Instance Op_Z_sgn : UnOp Z.sgn :=
  { TUOp := Z.sgn ; TUOpInj _ := eq_refl }.
Add Zify UnOp Op_Z_sgn.

#[global]
Instance Op_Z_pow : BinOp Z.pow :=
  { TBOp := Z.pow ; TBOpInj _ _ := eq_refl }.
Add Zify BinOp Op_Z_pow.

#[global]
Instance Op_Z_pow_pos : BinOp Z.pow_pos :=
  { TBOp := Z.pow ; TBOpInj _ _ := eq_refl }.
Add Zify BinOp Op_Z_pow_pos.

#[global]
Instance Op_Z_double : UnOp Z.double :=
  { TUOp := Z.mul 2 ; TUOpInj := Z.double_spec }.
Add Zify UnOp Op_Z_double.

#[global]
Instance Op_Z_pred_double : UnOp Z.pred_double :=
  { TUOp x := 2 * x - 1 ; TUOpInj := Z.pred_double_spec }.
Add Zify UnOp Op_Z_pred_double.

#[global]
Instance Op_Z_succ_double : UnOp Z.succ_double :=
  { TUOp x := 2 * x + 1 ; TUOpInj := Z.succ_double_spec }.
Add Zify UnOp Op_Z_succ_double.

#[global]
Instance Op_Z_square : UnOp Z.square :=
  { TUOp x := x * x ; TUOpInj := Z.square_spec }.
Add Zify UnOp Op_Z_square.

#[global]
Instance Op_Z_div2 : UnOp Z.div2 :=
  { TUOp x := x / 2 ; TUOpInj := Z.div2_div }.
Add Zify UnOp Op_Z_div2.

#[global]
Instance Op_Z_quot2 : UnOp Z.quot2 :=
  { TUOp x := Z.quot x 2 ; TUOpInj := Zeven.Zquot2_quot }.
Add Zify UnOp Op_Z_quot2.

Lemma of_nat_to_nat_eq x : Z.of_nat (Z.to_nat x) = Z.max 0 x.
Proof.
  destruct x; simpl.
  - reflexivity.
  - now rewrite positive_nat_Z.
  - reflexivity.
Qed.

#[global]
Instance Op_Z_to_nat : UnOp Z.to_nat :=
  { TUOp x := Z.max 0 x ; TUOpInj := of_nat_to_nat_eq }.
Add Zify UnOp Op_Z_to_nat.

#[global]
Instance Op_Z_to_pos : UnOp Z.to_pos :=
  { TUOp x := Z.max 1 x ;
    TUOpInj x := ltac:(now simpl; destruct x;
                       [| rewrite <- Pos2Z.inj_max; rewrite Pos.max_1_l |]) }.
Add Zify UnOp Op_Z_to_pos.

(** Specification of derived operators over Z *)

#[global]
Instance ZmaxSpec : BinOpSpec Z.max :=
  { BPred n m r := n < m /\ r = m \/ m <= n /\ r = n ; BSpec := Z.max_spec }.
Add Zify BinOpSpec ZmaxSpec.

#[global]
Instance ZminSpec : BinOpSpec Z.min :=
  { BPred n m r := n < m /\ r = n \/ m <= n /\ r = m ; BSpec := Z.min_spec }.
Add Zify BinOpSpec ZminSpec.

#[global]
Instance ZsgnSpec : UnOpSpec Z.sgn :=
  { UPred n r := 0 < n /\ r = 1 \/ 0 = n /\ r = 0 \/ n < 0 /\ r = - 1 ;
    USpec := Z.sgn_spec }.
Add Zify UnOpSpec ZsgnSpec.

#[global]
Instance ZabsSpec : UnOpSpec Z.abs :=
  { UPred n r := 0 <= n /\ r = n \/ n < 0 /\ r = - n ; USpec := Z.abs_spec }.
Add Zify UnOpSpec ZabsSpec.

(** Saturate positivity constraints *)

#[global]
Instance SatPowPos : Saturate Z.pow :=
  { PArg1 x := 0 < x;
    PArg2 y := 0 <= y;
    PRes _ _ r := 0 < r;
    SatOk := fun x y => Z.pow_pos_nonneg x y}.
Add Zify Saturate SatPowPos.

#[global]
Instance SatPowNonneg : Saturate Z.pow :=
  { PArg1 x := 0 <= x;
    PArg2 y := True;
    PRes _ _ r := 0 <= r;
    SatOk a b Ha _ := @Z.pow_nonneg a b Ha }.
Add Zify Saturate SatPowNonneg.

(* TODO #14736 for compatibility only, should be removed after deprecation *)

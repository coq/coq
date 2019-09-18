(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Instances of [ZifyClasses] for emulating the existing zify.
   Each instance is registered using a Add 'class' 'name_of_instance'.
 *)

Require Import Arith Max Min BinInt BinNat Znat Nnat.
Require Import ZifyClasses.
Declare ML Module "zify_plugin".
Open Scope Z_scope.

(** Propositional logic *)
Instance PropAnd : PropOp and.
Proof.
  constructor.
  tauto.
Defined.
Add PropOp PropAnd.

Instance PropOr : PropOp or.
Proof.
  constructor.
  tauto.
Defined.
Add PropOp PropOr.

Instance PropArrow : PropOp (fun x y => x -> y).
Proof.
  constructor.
  intros.
  tauto.
Defined.
Add PropOp PropArrow.

Instance PropIff : PropOp iff.
Proof.
  constructor.
  intros.
  tauto.
Defined.
Add PropOp PropIff.

Instance PropNot : PropUOp not.
Proof.
  constructor.
  intros.
  tauto.
Defined.
Add PropUOp PropNot.


Instance Inj_Z_Z : InjTyp Z Z :=
  mkinj _ _ (fun x => x) (fun x =>  True ) (fun _ => I).
Add InjTyp Inj_Z_Z.

(** Support for nat *)

Instance Inj_nat_Z : InjTyp nat Z :=
  mkinj _ _ Z.of_nat (fun x =>  0 <= x ) Nat2Z.is_nonneg.
Add InjTyp Inj_nat_Z.

(* zify_nat_rel *)
Instance Op_ge : BinRel ge :=
  {| TR := Z.ge; TRInj := Nat2Z.inj_ge |}.
Add BinRel Op_ge.

Instance Op_lt : BinRel lt :=
  {| TR := Z.lt; TRInj := Nat2Z.inj_lt |}.
Add BinRel Op_lt.

Instance Op_gt : BinRel gt :=
  {| TR := Z.gt; TRInj := Nat2Z.inj_gt |}.
Add BinRel Op_gt.

Instance Op_le : BinRel le :=
  {| TR := Z.le; TRInj := Nat2Z.inj_le |}.
Add BinRel Op_le.

Instance Op_eq_nat : BinRel (@eq nat) :=
  {| TR := @eq Z ; TRInj := fun x y : nat => iff_sym (Nat2Z.inj_iff x y) |}.
Add BinRel Op_eq_nat.

(* zify_nat_op *)
Instance Op_plus : BinOp Nat.add :=
  {| TBOp := Z.add; TBOpInj := Nat2Z.inj_add |}.
Add BinOp Op_plus.

Instance Op_sub : BinOp Nat.sub :=
  {| TBOp := fun n m => Z.max 0 (n - m) ; TBOpInj := Nat2Z.inj_sub_max |}.
Add BinOp Op_sub.

Instance Op_mul : BinOp Nat.mul :=
  {| TBOp := Z.mul ; TBOpInj := Nat2Z.inj_mul |}.
Add BinOp Op_mul.

Instance Op_min : BinOp Nat.min :=
  {| TBOp := Z.min ; TBOpInj := Nat2Z.inj_min |}.
Add BinOp Op_min.

Instance Op_max : BinOp Nat.max :=
  {| TBOp := Z.max ; TBOpInj := Nat2Z.inj_max |}.
Add BinOp Op_max.

Instance Op_pred : UnOp Nat.pred :=
  {| TUOp := fun n => Z.max 0 (n - 1) ; TUOpInj := Nat2Z.inj_pred_max |}.
Add UnOp Op_pred.

Instance Op_S : UnOp S :=
  {| TUOp := fun x => Z.add x 1 ; TUOpInj := Nat2Z.inj_succ |}.
Add UnOp Op_S.

Instance Op_O : CstOp O :=
  {| TCst := Z0 ; TCstInj := eq_refl (Z.of_nat 0) |}.

Instance Op_Z_abs_nat : UnOp  Z.abs_nat :=
  { TUOp := Z.abs ; TUOpInj := Zabs2Nat.id_abs }.
Add UnOp Op_Z_abs_nat.

(** Support for positive *)

Instance Inj_pos_Z : InjTyp positive Z :=
  {| inj := Zpos ; pred := (fun x =>  0 < x ) ; cstr := Pos2Z.pos_is_pos |}.
Add InjTyp Inj_pos_Z.

Instance Op_pos_to_nat : UnOp  Pos.to_nat :=
  {TUOp := (fun x => x); TUOpInj := positive_nat_Z}.
Add UnOp Op_pos_to_nat.

Instance Inj_N_Z : InjTyp N Z :=
  mkinj _ _ Z.of_N (fun x =>  0 <= x ) N2Z.is_nonneg.
Add InjTyp Inj_N_Z.


Instance Op_N_to_nat : UnOp  N.to_nat :=
  { TUOp := fun x => x ; TUOpInj := N_nat_Z }.
Add UnOp Op_N_to_nat.

(* zify_positive_rel *)

Instance Op_pos_ge : BinRel Pos.ge :=
  {| TR := Z.ge; TRInj := fun x y => iff_refl (Z.pos x >= Z.pos y) |}.
Add BinRel Op_pos_ge.

Instance Op_pos_lt : BinRel Pos.lt :=
  {| TR := Z.lt; TRInj := fun x y => iff_refl (Z.pos x < Z.pos y) |}.
Add BinRel Op_pos_lt.

Instance Op_pos_gt : BinRel Pos.gt :=
  {| TR := Z.gt; TRInj := fun x y => iff_refl (Z.pos x > Z.pos y)  |}.
Add BinRel Op_pos_gt.

Instance Op_pos_le : BinRel Pos.le :=
  {| TR := Z.le; TRInj := fun x y => iff_refl (Z.pos x <= Z.pos y) |}.
Add BinRel Op_pos_le.

Instance Op_eq_pos : BinRel (@eq positive) :=
  {| TR := @eq Z ; TRInj := fun x y  => iff_sym (Pos2Z.inj_iff x y) |}.
Add BinRel Op_eq_pos.

(* zify_positive_op *)


Program Instance Op_Z_of_N : UnOp Z.of_N :=
  { TUOp := (fun x => x) ; TUOpInj := fun x => eq_refl (Z.of_N x) }.
Add UnOp Op_Z_of_N.

Instance Op_Z_neg : UnOp Z.neg :=
  { TUOp :=  Z.opp ; TUOpInj := (fun x => eq_refl (Zneg x))}.
Add UnOp Op_Z_neg.

Instance Op_Z_pos : UnOp Z.pos :=
  { TUOp := (fun x =>  x) ; TUOpInj := (fun x => eq_refl (Z.pos x))}.
Add UnOp Op_Z_pos.

Instance Op_pos_succ : UnOp Pos.succ :=
  { TUOp := fun x => x + 1; TUOpInj := Pos2Z.inj_succ  }.
Add UnOp Op_pos_succ.

Instance Op_pos_pred : UnOp Pos.pred :=
  { TUOp := fun x => Z.max 1 (x - 1) ;
    TUOpInj := ltac :
                 (intros;
                    rewrite <- Pos.sub_1_r;
                    apply Pos2Z.inj_sub_max) }.
Add UnOp Op_pos_pred.

Instance Op_pos_of_succ_nat : UnOp Pos.of_succ_nat :=
  { TUOp := fun x => x + 1 ; TUOpInj := Zpos_P_of_succ_nat }.
Add UnOp Op_pos_of_succ_nat.

Program Instance Op_pos_add : BinOp Pos.add :=
  { TBOp := Z.add ; TBOpInj := ltac: (reflexivity) }.
Add BinOp Op_pos_add.

Instance Op_pos_sub : BinOp Pos.sub :=
  { TBOp := fun n m => Z.max 1 (n - m) ;TBOpInj := Pos2Z.inj_sub_max }.
Add BinOp Op_pos_sub.

Instance Op_pos_mul : BinOp Pos.mul :=
  { TBOp :=  Z.mul ; TBOpInj := ltac: (reflexivity) }.
Add BinOp Op_pos_mul.

Instance Op_pos_min : BinOp Pos.min :=
  { TBOp := Z.min ; TBOpInj := Pos2Z.inj_min }.
Add BinOp Op_pos_min.

Instance Op_pos_max : BinOp Pos.max :=
  { TBOp := Z.max ; TBOpInj := Pos2Z.inj_max }.
Add BinOp Op_pos_max.

Instance Op_xO : UnOp xO :=
  { TUOp := fun x => 2 * x ; TUOpInj := ltac: (reflexivity) }.
Add UnOp Op_xO.

Instance Op_xI : UnOp xI :=
  { TUOp := fun x => 2 * x + 1 ; TUOpInj := ltac: (reflexivity) }.
Add UnOp Op_xI.

Instance Op_xH : CstOp xH :=
  { TCst := 1%Z ; TCstInj := ltac:(reflexivity)}.
Add CstOp Op_xH.

Instance Op_Z_of_nat : UnOp Z.of_nat:=
  { TUOp := fun x => x ; TUOpInj := ltac:(reflexivity) }.
Add UnOp Op_Z_of_nat.

(* zify_N_rel *)
Instance Op_N_ge : BinRel N.ge :=
  {| TR := Z.ge ; TRInj := N2Z.inj_ge |}.
Add BinRel Op_N_ge.

Instance Op_N_lt : BinRel N.lt :=
  {| TR := Z.lt ; TRInj := N2Z.inj_lt |}.
Add BinRel Op_N_lt.

Instance Op_N_gt : BinRel N.gt :=
  {| TR := Z.gt ; TRInj := N2Z.inj_gt |}.
Add BinRel Op_N_gt.

Instance Op_N_le : BinRel N.le :=
  {| TR := Z.le ; TRInj := N2Z.inj_le |}.
Add BinRel Op_N_le.

Instance Op_eq_N : BinRel (@eq N) :=
  {| TR := @eq Z ; TRInj := fun x y : N => iff_sym (N2Z.inj_iff x y) |}.
Add BinRel Op_eq_N.

(* zify_N_op *)
Instance Op_N_of_nat : UnOp  N.of_nat :=
  { TUOp := fun x => x ; TUOpInj := nat_N_Z }.
Add UnOp Op_N_of_nat.

Instance Op_Z_abs_N : UnOp Z.abs_N :=
  { TUOp := Z.abs ; TUOpInj := N2Z.inj_abs_N }.
Add UnOp Op_Z_abs_N.

Instance Op_N_pos : UnOp N.pos :=
  { TUOp := fun x => x ; TUOpInj := ltac:(reflexivity)}.
Add UnOp Op_N_pos.

Instance Op_N_add : BinOp N.add :=
  {| TBOp := Z.add ; TBOpInj := N2Z.inj_add |}.
Add BinOp Op_N_add.

Instance Op_N_min : BinOp N.min :=
  {| TBOp := Z.min ; TBOpInj := N2Z.inj_min |}.
Add BinOp Op_N_min.

Instance Op_N_max : BinOp N.max :=
  {| TBOp := Z.max ; TBOpInj := N2Z.inj_max |}.
Add BinOp Op_N_max.

Instance Op_N_mul : BinOp N.mul :=
  {| TBOp := Z.mul ; TBOpInj := N2Z.inj_mul |}.
Add BinOp Op_N_mul.

Instance Op_N_sub : BinOp N.sub :=
  {| TBOp := fun x y => Z.max 0 (x - y) ; TBOpInj := N2Z.inj_sub_max|}.
Add BinOp Op_N_sub.

Instance Op_N_div : BinOp N.div :=
  {| TBOp := Z.div ; TBOpInj := N2Z.inj_div|}.
Add BinOp Op_N_div.



Instance Op_N_mod : BinOp N.modulo :=
  {| TBOp := Z.rem ; TBOpInj := N2Z.inj_rem|}.
Add BinOp Op_N_mod.

Instance Op_N_pred : UnOp N.pred :=
  { TUOp := fun x  => Z.max 0 (x - 1) ;
    TUOpInj :=
      ltac:(intros; rewrite N.pred_sub; apply N2Z.inj_sub_max) }.
Add UnOp Op_N_pred.

Instance Op_N_succ : UnOp N.succ :=
  {| TUOp := fun x => x + 1 ; TUOpInj := N2Z.inj_succ |}.
Add UnOp Op_N_succ.

(** Support for Z - injected to itself *)

(* zify_Z_rel *)
Instance Op_Z_ge : BinRel Z.ge :=
  {| TR := Z.ge ; TRInj := fun x y  => iff_refl (x>= y)|}.
Add BinRel Op_Z_ge.

Instance Op_Z_lt : BinRel Z.lt :=
  {| TR := Z.lt ;  TRInj := fun x y  => iff_refl (x < y)|}.
Add BinRel Op_Z_lt.

Instance Op_Z_gt : BinRel Z.gt :=
  {| TR := Z.gt ;TRInj := fun x y  => iff_refl (x > y)|}.
Add BinRel Op_Z_gt.

Instance Op_Z_le : BinRel Z.le :=
  {| TR := Z.le ;TRInj := fun x y  => iff_refl (x <= y)|}.
Add BinRel Op_Z_le.

Instance Op_eqZ : BinRel (@eq Z) :=
  { TR := @eq Z ; TRInj := fun x y  => iff_refl (x = y) }.
Add BinRel Op_eqZ.

Instance Op_Z_add : BinOp Z.add :=
  { TBOp := Z.add  ; TBOpInj := ltac:(reflexivity) }.
Add BinOp Op_Z_add.

Instance Op_Z_min : BinOp Z.min :=
  { TBOp := Z.min ; TBOpInj := ltac:(reflexivity) }.
Add BinOp Op_Z_min.

Instance Op_Z_max : BinOp Z.max :=
  { TBOp := Z.max ; TBOpInj := ltac:(reflexivity) }.
Add BinOp Op_Z_max.

Instance Op_Z_mul : BinOp Z.mul :=
  { TBOp := Z.mul ; TBOpInj := ltac:(reflexivity) }.
Add BinOp Op_Z_mul.

Instance Op_Z_sub : BinOp Z.sub :=
  { TBOp := Z.sub ; TBOpInj := ltac:(reflexivity) }.
Add BinOp Op_Z_sub.

Instance Op_Z_div : BinOp Z.div :=
  { TBOp := Z.div ; TBOpInj := ltac:(reflexivity) }.
Add BinOp Op_Z_div.

Instance Op_Z_mod : BinOp Z.modulo :=
  { TBOp := Z.modulo ; TBOpInj := ltac:(reflexivity) }.
Add BinOp Op_Z_mod.

Instance Op_Z_rem : BinOp Z.rem :=
  { TBOp := Z.rem ; TBOpInj := ltac:(reflexivity) }.
Add BinOp Op_Z_rem.

Instance Op_Z_quot : BinOp Z.quot :=
  { TBOp := Z.quot ; TBOpInj := ltac:(reflexivity) }.
Add BinOp Op_Z_quot.

Instance Op_Z_succ : UnOp Z.succ :=
  { TUOp := fun x => x + 1 ; TUOpInj := ltac:(reflexivity) }.
Add UnOp Op_Z_succ.

Instance Op_Z_pred : UnOp Z.pred :=
  { TUOp := fun x => x - 1 ; TUOpInj := ltac:(reflexivity) }.
Add UnOp Op_Z_pred.

Instance Op_Z_opp : UnOp Z.opp :=
  { TUOp := Z.opp ; TUOpInj := ltac:(reflexivity) }.
Add UnOp Op_Z_opp.

Instance Op_Z_abs : UnOp Z.abs :=
  { TUOp := Z.abs ; TUOpInj := ltac:(reflexivity) }.
Add UnOp Op_Z_abs.

Instance Op_Z_sgn : UnOp Z.sgn :=
  { TUOp := Z.sgn ; TUOpInj := ltac:(reflexivity) }.
Add UnOp Op_Z_sgn.

Instance Op_Z_pow_pos : BinOp Z.pow_pos :=
  { TBOp := Z.pow ; TBOpInj := ltac:(reflexivity) }.
Add BinOp Op_Z_pow_pos.

Lemma of_nat_to_nat_eq : forall x,  Z.of_nat (Z.to_nat x) = Z.max 0 x.
Proof.
  destruct x.
  - reflexivity.
  - rewrite Z2Nat.id.
    reflexivity.
    compute. congruence.
  - reflexivity.
Qed.

Instance Op_Z_to_nat : UnOp Z.to_nat :=
  { TUOp := fun x => Z.max 0 x ; TUOpInj := of_nat_to_nat_eq }.
Add UnOp Op_Z_to_nat.

(** Specification of derived operators over Z *)

Instance ZmaxSpec : BinOpSpec Z.max :=
  {| BPred := fun n m r => n < m /\ r = m \/ m <= n /\ r = n ; BSpec := Z.max_spec|}.
Add Spec ZmaxSpec.

Instance ZminSpec : BinOpSpec Z.min :=
  {| BPred := fun n m r : Z => n < m /\ r = n \/ m <= n /\ r = m ;
     BSpec := Z.min_spec|}.
Add Spec ZminSpec.

Instance ZsgnSpec : UnOpSpec Z.sgn :=
  {| UPred := fun n r : Z => 0 < n /\ r = 1 \/ 0 = n /\ r = 0 \/ n < 0 /\ r = - (1) ;
     USpec := Z.sgn_spec|}.
Add Spec ZsgnSpec.

Instance ZabsSpec : UnOpSpec Z.abs :=
  {| UPred := fun n r: Z =>  0 <= n /\ r = n \/ n < 0 /\ r = - n ;
     USpec := Z.abs_spec|}.
Add Spec ZabsSpec.

(** Saturate positivity constraints *)

Instance SatProd : Saturate Z.mul :=
  {|
    PArg1 := fun x => 0 <= x;
    PArg2 := fun y => 0 <= y;
    PRes  := fun r => 0 <= r;
    SatOk := Z.mul_nonneg_nonneg
  |}.
Add Saturate SatProd.

Instance SatProdPos : Saturate Z.mul :=
  {|
    PArg1 := fun x => 0 < x;
    PArg2 := fun y => 0 < y;
    PRes  := fun r => 0 < r;
    SatOk := Z.mul_pos_pos
  |}.
Add Saturate SatProdPos.

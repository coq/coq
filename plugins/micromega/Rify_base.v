(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Instances of [ZifyClasses] for the rify tactic i.e. an instance of zify
   but over R.
 *)
Require Import ZifyClasses.
Declare ML Module "zify_plugin".
Require Import ZifyProp.
Require Import BinInt Reals Lra.

(** Know operators over R *)

Instance Inj_R_R : InjTyp R R:=
     {| inj := (fun x => x) ; pred :=(fun x =>  True ) ; cstr := (fun _ => I) |}.
Add InjTyp Inj_R_R.

Instance Op_eq_R : BinRel (@eq R) :=
  {| TR := @eq R ; TRInj := fun x y  => iff_refl (x = y) |}.
Add BinRel Op_eq_R.

Instance Op_Rle : BinRel Rle :=
  { TR := Rle ; TRInj := fun x y => iff_refl (Rle x y)}.
Add BinRel Op_Rle.

Instance Op_Rge : BinRel Rge :=
  { TR := Rge ; TRInj := fun x y => iff_refl (Rge x y)}.
Add BinRel Op_Rge.

Instance Op_Rlt : BinRel Rlt :=
  { TR := Rlt ; TRInj := fun x y => iff_refl (Rlt x y)}.
Add BinRel Op_Rlt.

Instance Op_Rgt : BinRel Rgt :=
  { TR := Rgt ; TRInj := fun x y => iff_refl (Rgt x y)}.
Add BinRel Op_Rgt.

Instance Op_Rplus : BinOp Rplus :=
{ TBOp := Rplus; TBOpInj := ltac: (reflexivity) }.
Add BinOp Op_Rplus.

Instance Op_Rmult : BinOp Rmult :=
{ TBOp := Rmult; TBOpInj := ltac: (reflexivity) }.
Add BinOp Op_Rmult.

Instance Op_Rminus : BinOp Rminus :=
{ TBOp := Rminus; TBOpInj := ltac: (reflexivity) }.
Add BinOp Op_Rminus.

Instance Op_Rpower : BinOp Rpower :=
{ TBOp := Rpower; TBOpInj := ltac: (reflexivity) }.
Add BinOp Op_Rpower.

Instance Op_Rmax : BinOp Rmax :=
{ TBOp := Rmax; TBOpInj := ltac: (reflexivity) }.
Add BinOp Op_Rmax.

Instance Op_Rmin : BinOp Rmin :=
{ TBOp := Rmin; TBOpInj := ltac: (reflexivity) }.
Add BinOp Op_Rmin.

Instance Op_Rdiv : BinOp Rdiv :=
{ TBOp := Rdiv; TBOpInj := ltac: (reflexivity) }.
Add BinOp Op_Rdiv.

Instance Op_Ropp : UnOp Ropp :=
{ TUOp := Ropp; TUOpInj := ltac: (reflexivity) }.
Add UnOp Op_Ropp.

Instance Op_Rinv : UnOp Rinv :=
  { TUOp := Rinv; TUOpInj := ltac: (reflexivity) }.
Add UnOp Op_Rinv.

(** Operators over [nat] *)
Instance Inj_nat_R : InjTyp nat R:=
  {| inj := INR ; pred :=(fun x =>  (0 <= x)%R) ; cstr := pos_INR |}.
Add InjTyp Inj_nat_R.

Instance Op_INR : UnOp INR:=
{ TUOp := (fun x => x); TUOpInj := ltac: (reflexivity) }.
Add UnOp Op_INR.

Instance Op_plus : BinOp plus :=
  { TBOp := Rplus ; TBOpInj := plus_INR}.
Add BinOp Op_plus.

Instance Op_mult : BinOp mult :=
  { TBOp := Rmult ; TBOpInj := mult_INR}.
Add BinOp Op_mult.

Instance Op_S : UnOp S :=
  { TUOp := fun x => (1 + x)%R; TUOpInj := S_O_plus_INR }.
Add UnOp Op_S.

Instance Op_O : CstOp O :=
  { TCst := R0; TCstInj := ltac:(reflexivity) }.
Add CstOp Op_O.

Lemma minus_INR_Rmax :
  forall n m,
         INR (n - m)%nat =  Rmax 0 (INR n - INR m).
Proof.
  intros.
  apply Rmax_case_strong.
  - intros.
    replace (n - m)%nat with 0.
    reflexivity.
    apply Rminus_le in H.
    apply INR_le in H.
    rewrite <- Nat.sub_0_le in H.
    congruence.
  -  intros.
     apply minus_INR.
     apply INR_le.
     lra.
Qed.

Instance Op_minus : BinOp minus :=
  { TBOp := (fun x y => Rmax 0 (Rminus x y)) ; TBOpInj := minus_INR_Rmax}.
Add BinOp Op_minus.

(** Operators over [positive] *)
Lemma IPR_2_le : forall x, (1 <= IPR_2 x)%R.
Proof.
  induction x; simpl; lra.
Qed.

Lemma IPR_le : forall x, (1 <= IPR x)%R.
Proof.
  intros.
  unfold IPR.
  destruct x; try specialize (IPR_2_le x); lra.
Qed.

Instance Inj_P_R : InjTyp positive R:=
  { inj := IPR ; pred :=(fun x =>  (1 <= x)%R ) ; cstr := IPR_le }.
Add InjTyp Inj_P_R.

(** Operators over [Z] *)

Instance Inj_Z_R : InjTyp Z R:=
  { inj := IZR ; pred :=(fun x =>  True ) ; cstr := (fun _ => I) }.
Add InjTyp Inj_Z_R.


Instance Op_IZR : UnOp IZR:=
{ TUOp := (fun x => x); TUOpInj := (fun x => eq_refl (IZR x)) }.
Add UnOp Op_IZR.

Instance Op_Z_opp : UnOp Z.opp :=
{ TUOp := Ropp; TUOpInj := opp_IZR }.
Add UnOp Op_Z_opp.

Instance Op_Z_add : BinOp Z.add:=
{ TBOp := Rplus ; TBOpInj := plus_IZR }.
Add BinOp Op_Z_add.

Instance Op_Z_sub : BinOp Z.sub:=
{ TBOp := Rminus ; TBOpInj := minus_IZR }.
Add BinOp Op_Z_sub.

Instance Op_Z_mul : BinOp Z.mul:=
{ TBOp := Rmult ; TBOpInj := mult_IZR }.
Add BinOp Op_Z_mul.

(** Specifications *)
Lemma Rmin_lem : forall (x y:R),
    ((x <= y) /\ Rmin x y = x \/ (y <= x)%R /\ Rmin x y = y)%R.
Proof.
  intros.
  apply Rmin_case_strong.
  lra.
  lra.
Qed.

Lemma Rmax_lem : forall (x y:R),
    ((x <= y) /\ Rmax x y = y \/ (y <= x)%R /\ Rmax x y = x)%R.
Proof.
  intros.
  apply Rmax_case_strong.
  lra.
  lra.
Qed.

Instance Rmin_spec : BinOpSpec Rmin :=
  { BPred := (fun x y r => (x <= y /\ r = x) \/ (y <= x /\ r = y))%R; BSpec := Rmin_lem}.
Add Spec Rmin_spec.

Instance Rmax_spec : BinOpSpec Rmax :=
  { BPred := (fun x y r => (x <= y /\ r = y) \/ (y <= x /\ r = x))%R; BSpec := Rmax_lem}.
Add Spec Rmax_spec.

Instance Rinv_spec : UnOpSpec Rinv :=
  { UPred := (fun x r => x <> 0%R -> 1 = x  * r)%R ; USpec := Rinv_r_sym}.
Add Spec Rinv_spec.

Lemma Rdiv_lem : forall x y,
    (y <> 0 -> x = (x / y) *y)%R.
Proof.
  unfold Rdiv.
  intros. rewrite Rmult_assoc.
  rewrite <- Rinv_l_sym by  auto.
  ring.
Qed.

Instance Rdiv_spec : BinOpSpec Rdiv :=
  { BPred := (fun x y r => y <> 0%R -> x = r *y)%R ; BSpec := Rdiv_lem}.
Add Spec Rdiv_spec.

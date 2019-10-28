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

(** Over R, there are quite a few power function
    which are sometimes more defined than [Rpower].
    In other to inject those, we defined [Rpower_ext]
    which is a conservative extension of Rpower *)

Definition Reven (n : R) :=
  Z.even ((Int_part n))%Z.

Definition pow_neg_one (n : R) :=
  if Reven n then 1%R else (-1)%R.

Definition Rpower0 (y : R) :=
  if Req_EM_T y 0 then 1%R else 0%R.

Inductive Rsign {x : R} : Type :=
| LTZ : (x < 0)%R -> @Rsign x
| EQZ : (x = 0)%R -> @Rsign x
| ZLT : (0 < x)%R -> @Rsign x.


Lemma not_lt_not_eq_0lt : forall x,
     ~ (x < 0)%R ->
     x <> 0%R ->
     (0 < x)%R.
Proof.
  intros.
  lra.
Qed.

Definition Rsign_dec (x  : R) : @Rsign x:=
    match Rlt_dec x 0 with
    | left  p => LTZ p
    | right p => match Req_EM_T x 0 with
                 | left p => EQZ p
                 | right p' => @ZLT x (ltac:(lra))
                 end
    end.

Definition RpowerZ (x y : R) :=
  match Rsign_dec x with
  | LTZ _ => if Rlt_dec y 0 then 0%R
             else  (pow_neg_one y * Rpower (Ropp x) y)%R
  | EQZ _ => Rpower0 y
  | ZLT _ => if Rlt_dec y 0 then 0%R else Rpower x y
  end.

Lemma INR_Rpower0 : forall m,  INR (0 ^ m) = Rpower0 (INR m).
Proof.
  unfold Rpower0.
  intros. destruct (Req_EM_T (INR m) 0).
  - change 0%R with (INR 0%nat) in e.
    apply INR_eq in e. subst ; reflexivity.
  - destruct m ; simpl in n ; try congruence.
    reflexivity.
Qed.

Lemma IZR_Rpower0 : forall m,  IZR (0 ^ m) = Rpower0 (IZR m).
Proof.
  unfold Rpower0.
  intros. destruct (Req_EM_T (IZR m) 0).
  -apply eq_IZR in e. subst ; reflexivity.
  - destruct m.
    + lra.
    + rewrite Z.pow_0_l.
      reflexivity.
      apply Pos2Z.pos_is_pos.
    + reflexivity.
Qed.


Ltac arith :=
  match goal with
  | |- (0 <= Z.pos _)%Z => compute ; congruence
  | |-  (0 < Pos.to_nat ?X)%nat => exact (Pos2Nat.is_pos X)
  | H : IZR (Z.pos _) = 0%R |- _ => apply eq_IZR in H
  | H : IZR (Z.neg _) = 0%R |- _ => apply eq_IZR in H
  | H : (IZR (Z.pos _) < 0)%R |- _ => apply lt_IZR in H
  | H : (INR ?X < 0)%R |- _ => change 0%R with (INR 0%nat) in H ;
                               apply INR_lt in  H ; apply Nat.nlt_0_r in H ; exfalso ; exact H
  | _ => try reflexivity
  end ; try discriminate; auto.


Lemma INR_pow : forall n m,
    INR (n ^ m) = RpowerZ (INR n) (INR m).
Proof.
  intros.
  unfold RpowerZ.
  destruct (Rsign_dec (INR n)); arith.
  - change 0%R with (INR 0) in e.
    apply INR_eq in e.
    subst. apply INR_Rpower0.
  - destruct (Rlt_dec (INR m) 0) ; arith.
    rewrite Rpower_pow by arith.
    apply pow_INR.
Qed.

Lemma Z_pow_Rpower : forall (n m:Z),
    (0 < n )%Z ->
    (0 <= m)%Z ->
    IZR (n ^ m) = Rpower (IZR n) (IZR m).
Proof.
  intros.
  rewrite <- (Z2Nat.id m) by auto.
  rewrite <- pow_IZR.
  rewrite <- Rpower_pow.
  f_equal.
  rewrite INR_IZR_INZ.
  reflexivity.
  apply IZR_lt;auto.
Qed.


Lemma Int_part_IZR_pos : forall (z:Z), (0 <= z)%Z -> Int_part (IZR z) = z.
Proof.
  intros.
  rewrite <- (Z2Nat.id z) at 1 by auto.
  rewrite <- INR_IZR_INZ.
  rewrite Int_part_INR.
  rewrite Z2Nat.id by auto.
  reflexivity.
Qed.

Lemma Int_part_IZR : forall (z:Z), Int_part (IZR z) = z.
Proof.
  intros.
  destruct (Z.nonpos_nonneg_cases z).
  -
    assert (0 <= - z)%Z.
    {     rewrite Z.opp_nonneg_nonpos; auto. }
    replace (IZR z) with (0 - (IZR (- z)%Z))%R.
    rewrite Rminus_Int_part1.
    change 0%R with (INR 0).
    rewrite Int_part_INR. simpl.
    rewrite Int_part_IZR_pos; auto.
    ring.
    rewrite fp_R0.
    unfold frac_part.
    rewrite Int_part_IZR_pos; auto.
    lra.
    rewrite opp_IZR.
    ring.
  -  apply Int_part_IZR_pos; auto.
Qed.

Lemma Reven_Zeven : forall m,
    Reven (IZR m) = Z.even m.
Proof.
  intros.
  unfold Reven.
  rewrite Int_part_IZR.
  reflexivity.
Qed.

Fixpoint Nat_even_S (n : nat) : Nat.even n = negb (Nat.even (S n)).
Proof.
  simpl.
  destruct n.
  - reflexivity.
  - rewrite (Nat_even_S n).
    rewrite Bool.negb_involutive.
    reflexivity.
Qed.

Fixpoint Z_power_nat_neg (n:nat) : forall x,
    Zpower.Zpower_nat (- x) n =
    (if Nat.even n then     Zpower.Zpower_nat x n else  - (Zpower.Zpower_nat x n))%Z.
Proof.
  destruct n.
  - simpl ; auto.
  - intros.
    rewrite !Zpower.Zpower_nat_succ_r.
    rewrite Z_power_nat_neg.
    rewrite Nat_even_S.
    destruct (Nat.even (S n)); simpl; ring.
Qed.

Lemma Z_even_nat_even : forall m,
    (0 <= m)%Z ->
    Z.even m = Nat.even (Z.to_nat m).
Proof.
  intros.
  destruct m ; simpl; auto.
  destruct p ; auto.
  - rewrite Pos2Nat.inj_xI.
    rewrite Nat.even_succ.
    change (2 * Pos.to_nat p) with (0 + 2 * Pos.to_nat p).
    rewrite Nat.odd_add_mul_2.
    reflexivity.
  - rewrite Pos2Nat.inj_xO.
    change (2 * Pos.to_nat p) with (0 + 2 * Pos.to_nat p).
    rewrite Nat.even_add_mul_2.
    reflexivity.
Qed.


Lemma Z_pow_neg : forall n m,
    (0 <= m)%Z ->
    ((- n) ^ m)%Z = (if Z.even m then n ^ m else - (n^m))%Z.
Proof.
  intros.
  rewrite <- (Z2Nat.id m) by auto.
  rewrite <- ! Zpower.Zpower_nat_Z.
  rewrite Z_power_nat_neg.
  rewrite Z_even_nat_even.
  rewrite (Z2Nat.id m) by auto.
  auto.
  rewrite (Z2Nat.id m) by auto.
  auto.
Qed.

Lemma pow_neg_one_0 : pow_neg_one 0 = 1%R.
Proof.
  unfold pow_neg_one.
  rewrite Reven_Zeven.
  reflexivity.
Qed.

Lemma RpowerZ_0 : forall x, RpowerZ x 0 = 1%R.
Proof.
  unfold RpowerZ; intros.
  destruct (Rsign_dec x).
  - destruct (Rlt_dec 0 0). lra.
    rewrite pow_neg_one_0.
    rewrite Rpower_O by lra. ring.
  - unfold Rpower0.
    destruct (Req_EM_T 0 0); auto.
    lra.
  - destruct (Rlt_dec 0 0). lra.
    apply Rpower_O. lra.
Qed.

Lemma IZR_pow : forall n m,
    IZR (Z.pow n  m) = RpowerZ (IZR n) (IZR m).
Proof.
  intros.
  unfold RpowerZ.
  destruct (Rsign_dec (IZR n)).
  - destruct (Rlt_dec (IZR m) 0).
    + destruct m ; simpl in *; arith; lra.
    +
    rewrite <- opp_IZR.
    assert (n < 0)%Z.
    { apply lt_IZR; auto. }
    assert (0 <= m)%Z.
    { apply le_IZR. lra. }
    rewrite <- (Z_pow_Rpower (- n)%Z); auto.
    * unfold pow_neg_one.
    rewrite Reven_Zeven.
    rewrite Z_pow_neg ; auto.
    destruct (Z.even m).
    ring.
    rewrite opp_IZR.
    ring.
    * rewrite Z.opp_pos_neg.
      apply lt_IZR; auto.
  - apply eq_IZR in e.
    subst. apply IZR_Rpower0.
  - destruct (Rlt_dec (IZR m) 0); arith.
    + destruct m; arith; lra.
    + apply Z_pow_Rpower.
      apply lt_IZR; lra.
      apply le_IZR; lra.
Qed.



Definition RpowerRZ (x y : R) :=
  match Rsign_dec x with
  | LTZ _ => (pow_neg_one y * Rpower (Ropp x) y)%R
  | EQZ _ => match Rsign_dec y  with
             | EQZ _ => 1%R
             | LTZ _ => (/0)%R
             | ZLT _ => 0%R
             end
  | ZLT _  => Rpower x y
  end.

Lemma pow_neg : forall n m,
    (n < 0)%R ->
    (n ^ m)%R = ((if Nat.even m then 1 else -1) * (- n) ^ m)%R.
Proof.
  induction m ; simpl.
  - intros. ring.
  - destruct m.
    intros. ring.
    intros.
    rewrite IHm ; auto.
    rewrite (Nat_even_S m).
    destruct (Nat.even (S m)); simpl; ring.
Qed.

Lemma IZRZ_pos : forall p, IZR (Z.pos p) = INR (Pos.to_nat p).
Proof.
  intros.
  rewrite <- positive_nat_Z.
  rewrite <- INR_IZR_INZ.
  reflexivity.
Qed.


Lemma IZR_powerRZ : forall n m,
  powerRZ n m = RpowerRZ n (IZR m).
Proof.
  unfold powerRZ, RpowerRZ.
  destruct m.
  - destruct (Rsign_dec n).
    + rewrite pow_neg_one_0.
      rewrite Rpower_O; lra.
    + destruct (Rsign_dec 0); lra.
    + rewrite Rpower_O by lra. reflexivity.
  - destruct (Rsign_dec n).
    + unfold pow_neg_one.
      rewrite Reven_Zeven.
      rewrite Z_even_nat_even by arith.
      rewrite (IZRZ_pos p).
      rewrite Rpower_pow by lra.
      rewrite Z2Nat.inj_pos.
      rewrite <- pow_neg; auto.
    + destruct (Rsign_dec (IZR (Z.pos p))); arith.
      subst.
      rewrite pow_i by arith.
      reflexivity.
    +  rewrite IZRZ_pos.
       rewrite Rpower_pow by lra.
       reflexivity.
  - destruct (Rsign_dec n).
    + unfold pow_neg_one.
      rewrite Reven_Zeven.
      change (Z.neg p) with (Z.opp (Z.pos p)).
      rewrite Z.even_opp.
      rewrite Z_even_nat_even by arith.
      unfold Z.to_nat.
      rewrite Ropp_Ropp_IZR.
      rewrite Rpower_Ropp.
      rewrite pow_neg; auto.
      rewrite (IZRZ_pos p).
      rewrite <- Rpower_pow by lra.
      destruct (Nat.even (Pos.to_nat  p)).
      rewrite !Rmult_1_l.  reflexivity.
      field.
      intro.
      unfold Rpower in H.
      generalize (exp_pos ((INR (Pos.to_nat p) * ln (- n)))).
      rewrite H.
      lra.
    + subst.
      destruct (Rsign_dec (IZR (Z.neg p))); arith.
      * rewrite pow_i by apply Pos2Nat.is_pos.
        reflexivity.
      * apply lt_IZR in r.
        discriminate.
    + change (Z.neg p) with (Z.opp (Z.pos p)).
      rewrite Ropp_Ropp_IZR.
      rewrite Rpower_Ropp.
      rewrite IZRZ_pos.
      rewrite <- Rpower_pow by lra.
      reflexivity.
Qed.

Instance Op_Nat_pow : BinOp Nat.pow :=
  { TBOp := RpowerZ ; TBOpInj := INR_pow}.
Add BinOp Op_Nat_pow.

Instance Op_Z_pow : BinOp Z.pow :=
  { TBOp := RpowerZ ; TBOpInj := IZR_pow}.
Add BinOp Op_Z_pow.

Program Instance Op_powerRZ : BinOp powerRZ :=
  { TBOp := RpowerRZ ; TBOpInj := IZR_powerRZ}.
Add BinOp Op_powerRZ.

Definition R_bool (b : bool) := if b then 1%R else 0%R.

(** Specification for RpowerZ and RpowerRZ *)


Definition Rbool (b:bool) := if b then 1%R else (-1)%R.

Definition RpowerZ_pred (n m r : R) :=
    ((n = 0%R -> (m = 0%R -> r = 1%R)
                /\
                (m <> 0%R -> r = 0%R))
  /\
  (n < 0%R ->
   ((m = 0%R -> r = 1%R)
    /\
    (m < 0%R  -> r = 0%R)
    /\
    (m > 0%R ->  r= (Rbool (Reven m)) * Rpower (-n) m)))
  /\
  (n > 0%R ->
   ((m = 0%R -> r = 1%R)
    /\
    (m < 0%R  -> r = 0%R)
    /\
    (m > 0%R ->  r= Rpower n m))))%R.

Lemma RpowerZ_pred_correct : forall n m,
    ((n = 0%R -> (m = 0%R -> RpowerZ n m = 1%R)
                /\
                (m <> 0%R -> RpowerZ n m = 0%R))
  /\
  (n < 0%R ->
   ((m = 0%R -> RpowerZ n m = 1%R)
    /\
    (m < 0%R  -> RpowerZ n m = 0%R)
    /\
    (m > 0%R ->  RpowerZ n m= (Rbool (Reven m)) * Rpower (-n) m)))
  /\
  (n > 0%R ->
   ((m = 0%R -> RpowerZ n m = 1%R)
    /\
    (m < 0%R  -> RpowerZ n m = 0%R)
    /\
    (m > 0%R ->  RpowerZ n m= Rpower n m))))%R.
Proof.
  unfold RpowerZ.
  intros.
  destruct (Rsign_dec n);
    try match goal with
    | |-context[Rlt_dec ?X ?Y] => destruct (Rlt_dec X Y)
    end ;  intuition subst ; try lra.
  - rewrite pow_neg_one_0.
    rewrite Rpower_O. ring. lra.
  - unfold Rpower0.
    destruct (Req_EM_T 0 0) ; lra.
  - unfold Rpower0.
    destruct (Req_EM_T m 0) ; lra.
  - rewrite Rpower_O ; lra.
Qed.

Instance RpowerZ_spec : BinOpSpec RpowerZ :=
  { BPred := RpowerZ_pred ; BSpec := RpowerZ_pred_correct}.
Add Spec RpowerZ_spec.


Definition RpowerRZ_pred ( n m r :R) :=
    ((n < 0%R ->  r= (Rbool (Reven m)) * Rpower (-n) m)
     /\
     (n = 0%R -> (m = 0%R -> r = 1%R)
                 /\
                 (m < 0%R -> r = /0%R)
                 /\
                 (0%R < m -> r = 0%R))
     /\
     (0%R < n  -> r= Rpower n m))%R.


Lemma RpowerRZ_pred_correct : forall n m,
    ((n < 0%R ->  RpowerRZ n m= (Rbool (Reven m)) * Rpower (-n) m)
     /\
     (n = 0%R -> (m = 0%R -> RpowerRZ n m = 1%R)
                 /\
                 (m < 0%R -> RpowerRZ n m = /0%R)
                 /\
                 (0%R < m -> RpowerRZ n m = 0%R))
     /\
     (0%R < n  -> RpowerRZ n m= Rpower n m))%R.
Proof.
  unfold RpowerRZ.
  intros.
  destruct (Rsign_dec n);
    try match goal with
    | |-context[Rsign_dec ?M] => destruct (Rsign_dec M)
    end ;  intuition subst ; try lra.
Qed.



Instance RpowerRZ_spec : BinOpSpec RpowerRZ :=
  { BPred := RpowerRZ_pred ; BSpec := RpowerRZ_pred_correct}.
Add Spec RpowerRZ_spec.

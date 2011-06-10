(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import ZArith_base.
Require Import Zpow_def.
Require Import BinInt.
Require Import BinNat.
Require Import Setoid.
Require Import BinList.
Require Import BinPos.
Require Import BinNat.
Require Import BinInt.
Require Import Setoid.
Require Export Ring2.
Require Export Ring2_polynom.
Import List.

Set Implicit Arguments.

(* An object to return when an expression is not recognized as a constant *)
Definition NotConstant := false.

(** Z is a ring and a setoid*)

Lemma Zsth : Setoid_Theory Z (@eq Z).
constructor;red;intros;subst;trivial.
Qed.

Instance Zops:@Ring_ops Z 0%Z 1%Z Zplus Zmult Zminus Zopp (@eq Z).

Instance Zr: (@Ring _ _ _ _ _ _ _ _ Zops).
constructor;
try (try apply Zsth;
   try (unfold respectful, Proper; unfold equality; unfold eq_notation in *;
  intros; try rewrite H; try rewrite H0; reflexivity)).
 exact Zplus_comm. exact Zplus_assoc.
 exact Zmult_1_l.  exact Zmult_1_r. exact Zmult_assoc.
 exact Zmult_plus_distr_l.  intros; apply Zmult_plus_distr_r.  exact Zminus_diag.
Defined.

(*Instance ZEquality: @Equality Z:= (@eq Z).*)

(** Two generic morphisms from Z to (abrbitrary) rings, *)
(**second one is more convenient for proofs but they are ext. equal*)
Section ZMORPHISM.
Context {R:Type}`{Ring R}.

 Ltac rrefl := reflexivity.

 Fixpoint gen_phiPOS1 (p:positive) : R :=
  match p with
  | xH => 1
  | xO p => (1 + 1) * (gen_phiPOS1 p)
  | xI p => 1 + ((1 + 1) * (gen_phiPOS1 p))
  end.

 Fixpoint gen_phiPOS (p:positive) : R :=
  match p with
  | xH => 1
  | xO xH => (1 + 1)
  | xO p => (1 + 1) * (gen_phiPOS p)
  | xI xH => 1 + (1 +1)
  | xI p => 1 + ((1 + 1) * (gen_phiPOS p))
  end.

 Definition gen_phiZ1 z :=
  match z with
  | Zpos p => gen_phiPOS1 p
  | Z0 => 0
  | Zneg p => -(gen_phiPOS1 p)
  end.

 Definition gen_phiZ z :=
  match z with
  | Zpos p => gen_phiPOS p
  | Z0 => 0
  | Zneg p => -(gen_phiPOS p)
  end.
 Notation "[ x ]" := (gen_phiZ x).

 Definition get_signZ z :=
  match z with
  | Zneg p => Some (Zpos p)
  | _ => None
  end.

   Ltac norm := gen_rewrite.
   Ltac add_push :=  gen_add_push.
Ltac rsimpl := simpl.

 Lemma same_gen : forall x, gen_phiPOS1 x == gen_phiPOS x.
 Proof.
  induction x;rsimpl.
  rewrite IHx. destruct x;simpl;norm.
  rewrite IHx;destruct x;simpl;norm.
  gen_reflexivity.
 Qed.

 Lemma ARgen_phiPOS_Psucc : forall x,
   gen_phiPOS1 (Psucc x) == 1 + (gen_phiPOS1 x).
 Proof.
  induction x;rsimpl;norm.
  rewrite IHx ;norm.
  add_push 1;gen_reflexivity.
 Qed.

 Lemma ARgen_phiPOS_add : forall x y,
   gen_phiPOS1 (x + y) == (gen_phiPOS1 x) + (gen_phiPOS1 y).
 Proof.
  induction x;destruct y;simpl;norm.
  rewrite Pplus_carry_spec.
  rewrite ARgen_phiPOS_Psucc.
  rewrite IHx;norm.
  add_push (gen_phiPOS1 y);add_push 1;gen_reflexivity.
  rewrite IHx;norm;add_push (gen_phiPOS1 y);gen_reflexivity.
  rewrite ARgen_phiPOS_Psucc;norm;add_push 1;gen_reflexivity.
  rewrite IHx;norm;add_push(gen_phiPOS1 y); add_push 1;gen_reflexivity.
  rewrite IHx;norm;add_push(gen_phiPOS1 y);gen_reflexivity.
  add_push 1;gen_reflexivity.
  rewrite ARgen_phiPOS_Psucc;norm;add_push 1;gen_reflexivity.
 Qed.

 Lemma ARgen_phiPOS_mult :
   forall x y, gen_phiPOS1 (x * y) == gen_phiPOS1 x * gen_phiPOS1 y.
 Proof.
  induction x;intros;simpl;norm.
  rewrite ARgen_phiPOS_add;simpl;rewrite IHx;norm.
  rewrite IHx;gen_reflexivity.
 Qed.


(*morphisms are extensionaly equal*)
 Lemma same_genZ : forall x, [x] == gen_phiZ1 x.
 Proof.
  destruct x;rsimpl; try rewrite same_gen; gen_reflexivity.
 Qed.

 Lemma gen_Zeqb_ok : forall x y,
   Zeq_bool x y = true -> [x] == [y].
 Proof.
  intros x y H7.
  assert (H10 := Zeq_bool_eq x y H7);unfold IDphi in H10.
  rewrite H10;gen_reflexivity.
 Qed.

 Lemma gen_phiZ1_add_pos_neg : forall x y,
 gen_phiZ1 (Z.pos_sub x y)
 == gen_phiPOS1 x + -gen_phiPOS1 y.
 Proof.
  intros x y.
  rewrite Z.pos_sub_spec.
  assert (HH0 := Pminus_mask_Gt x y). unfold Pos.gt in HH0.
  assert (HH1 := Pminus_mask_Gt y x). unfold Pos.gt in HH1.
  rewrite Pos.compare_antisym in HH1.
  destruct (Pos.compare_spec x y) as [HH|HH|HH].
  subst. rewrite ring_opp_def;gen_reflexivity.
  destruct HH1 as [h [HHeq1 [HHeq2 HHor]]];trivial.
  unfold Pminus; rewrite HHeq1;rewrite <- HHeq2.
  rewrite ARgen_phiPOS_add;simpl;norm.
  rewrite ring_opp_def;norm.
  destruct HH0 as [h [HHeq1 [HHeq2 HHor]]];trivial.
  unfold Pminus; rewrite HHeq1;rewrite <- HHeq2.
  rewrite ARgen_phiPOS_add;simpl;norm.
  add_push (gen_phiPOS1 h). rewrite ring_opp_def ; norm.
 Qed.
(*
Lemma gen_phiZ1_add_pos_neg : forall x y,
 gen_phiZ1
    match Pos.compare_cont x y Eq with
    | Eq => Z0
    | Lt => Zneg (y - x)
    | Gt => Zpos (x - y)
    end
 == gen_phiPOS1 x + -gen_phiPOS1 y.
 Proof.
  intros x y.
  assert (HH:= (Pcompare_Eq_eq x y)); assert (HH0 := Pminus_mask_Gt x y).
  generalize (Pminus_mask_Gt y x).
  replace Eq with (CompOpp Eq);[intro HH1;simpl|trivial].
  assert (Pos.compare_cont x y Eq = Gt -> (x > y)%positive).
  auto with *.
  assert (CompOpp(Pos.compare_cont x y Eq) = Gt -> (y > x)%positive).
  rewrite Pcompare_antisym . simpl.
  auto with *.
  destruct (Pos.compare_cont x y Eq).
  rewrite HH;trivial. rewrite ring_opp_def. rrefl.
  destruct HH1 as [h [HHeq1 [HHeq2 HHor]]];trivial. simpl in H8. auto.
  
  unfold Pminus; rewrite HHeq1;rewrite <- HHeq2.
  rewrite ARgen_phiPOS_add;simpl;norm.
  rewrite ring_opp_def;norm.
  destruct HH0 as [h [HHeq1 [HHeq2 HHor]]];trivial. auto.
  unfold Pminus; rewrite HHeq1;rewrite <- HHeq2.
  rewrite ARgen_phiPOS_add;simpl;norm.
  add_push (gen_phiPOS1 h);rewrite ring_opp_def; norm.
 Qed.
*)
 Lemma match_compOpp : forall x (B:Type) (be bl bg:B),
  match CompOpp x with Eq => be | Lt => bl | Gt => bg end
  = match x with Eq => be | Lt => bg | Gt => bl end.
 Proof. destruct x;simpl;intros;trivial. Qed.

 Lemma gen_phiZ_add : forall x y, [x + y] == [x] + [y].
 Proof.
  intros x y; repeat rewrite same_genZ; generalize x y;clear x y.
  induction x;destruct y;simpl;norm.
  apply ARgen_phiPOS_add.
  apply gen_phiZ1_add_pos_neg. 
   rewrite gen_phiZ1_add_pos_neg. rewrite ring_add_comm.
reflexivity.
 rewrite ARgen_phiPOS_add. rewrite ring_opp_add. reflexivity.
Qed.

Lemma gen_phiZ_opp : forall x, [- x] == - [x].
 Proof.
  intros x. repeat rewrite same_genZ. generalize x ;clear x.
  induction x;simpl;norm.
  rewrite ring_opp_opp.  gen_reflexivity.
 Qed.

 Lemma gen_phiZ_mul : forall x y, [x * y] == [x] * [y].
 Proof.
  intros x y;repeat rewrite same_genZ.
  destruct x;destruct y;simpl;norm;
  rewrite  ARgen_phiPOS_mult;try (norm;fail).
  rewrite ring_opp_opp ;gen_reflexivity.
 Qed.

 Lemma gen_phiZ_ext : forall x y : Z, x = y -> [x] == [y].
 Proof. intros;subst;gen_reflexivity. Qed.

(*proof that [.] satisfies morphism specifications*)
Global Instance gen_phiZ_morph :
(@Ring_morphism (Z:Type) R _ _ _ _ _ _ _ Zops Zr _ _ _ _ _ _ _ _ _ gen_phiZ) . (* beurk!*)
 apply Build_Ring_morphism; simpl;try gen_reflexivity.
   apply gen_phiZ_add. intros. rewrite ring_sub_def. 
replace (Zminus x y) with (x + (-y))%Z. rewrite gen_phiZ_add. 
rewrite gen_phiZ_opp.  rewrite ring_sub_def. gen_reflexivity.
reflexivity.
 apply gen_phiZ_mul. apply gen_phiZ_opp. apply gen_phiZ_ext. 
 Defined.

End ZMORPHISM.

Instance multiplication_phi_ring{R:Type}`{Ring R} : Multiplication  :=
  {multiplication x y := (gen_phiZ x) * y}.



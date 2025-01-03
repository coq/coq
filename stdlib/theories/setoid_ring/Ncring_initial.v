(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import BinInt.
Require Import Zpow_def.
Require Import BinInt.
Require Import BinNat.
Require Import Setoid.
Require Import BinList.
Require Import BinPos.
Require Import BinNat.
Require Import BinInt.
Require Import Setoid.
Require Export Ncring.
Require Export Ncring_polynom.

Require Zbool.

Set Implicit Arguments.

(* An object to return when an expression is not recognized as a constant *)
Definition NotConstant := false.

(** Z is a ring and a setoid*)

Lemma Zsth : Equivalence (@eq Z).
Proof. exact Z.eq_equiv. Qed.

#[global]
Instance Zops:@Ring_ops Z 0%Z 1%Z Z.add Z.mul Z.sub Z.opp (@eq Z).
Defined.

#[global]
Instance Zr: (@Ring _ _ _ _ _ _ _ _ Zops).
Proof.
constructor; try apply Zsth; try solve_proper.
- exact Z.add_comm.
- exact Z.add_assoc.
- exact Z.mul_1_l.
- exact Z.mul_1_r.
- exact Z.mul_assoc.
- exact Z.mul_add_distr_r.
- intros; apply Z.mul_add_distr_l.
- exact Z.sub_diag.
Defined.

(*Instance ZEquality: @Equality Z:= (@eq Z).*)

(** Two generic morphisms from Z to (arbitrary) rings, *)
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
 Declare Scope ZMORPHISM.
 Notation "[ x ]" := (gen_phiZ x) : ZMORPHISM.
 Open Scope ZMORPHISM.

 Definition get_signZ z :=
  match z with
  | Zneg p => Some (Zpos p)
  | _ => None
  end.

   Ltac norm := gen_rewrite.
   Ltac add_push :=  Ncring.gen_add_push.
Ltac rsimpl := simpl.

 Lemma same_gen : forall x, gen_phiPOS1 x == gen_phiPOS x.
 Proof.
  induction x;rsimpl.
  - rewrite IHx. destruct x;simpl;norm.
  - rewrite IHx;destruct x;simpl;norm.
  - reflexivity.
 Qed.

 Lemma ARgen_phiPOS_Psucc : forall x,
   gen_phiPOS1 (Pos.succ x) == 1 + (gen_phiPOS1 x).
 Proof.
  induction x; simpl.
  - now rewrite IHx, ring_distr_r, ring_mul_1_r, ring_add_assoc.
  - reflexivity.
  - now rewrite ring_mul_1_r.
 Qed.

 Lemma ARgen_phiPOS_add : forall x y,
   gen_phiPOS1 (x + y) == (gen_phiPOS1 x) + (gen_phiPOS1 y).
 Proof.
  induction x;destruct y;simpl.
  - rewrite Pos.add_carry_spec, ARgen_phiPOS_Psucc, IHx.
    rewrite !ring_distr_r, !ring_mul_1_r, !ring_add_assoc.
    now add_push 1.
  - now rewrite IHx, !ring_distr_r, !ring_add_assoc.
  - rewrite ARgen_phiPOS_Psucc, !ring_distr_r, !ring_mul_1_r.
    now add_push 1.
  - rewrite IHx, !ring_distr_r, !ring_add_assoc.
    now add_push 1.
  - now rewrite IHx, !ring_distr_r.
  - now rewrite ring_add_comm.
  - now rewrite ARgen_phiPOS_Psucc, !ring_distr_r, !ring_mul_1_r, !ring_add_assoc.
  - reflexivity.
  - now rewrite ring_mul_1_r.
 Qed.

 Lemma ARgen_phiPOS_mult :
   forall x y, gen_phiPOS1 (x * y) == gen_phiPOS1 x * gen_phiPOS1 y.
 Proof.
  induction x; intros; simpl.
  - rewrite ARgen_phiPOS_add. simpl.
    now rewrite IHx, !ring_distr_l, !ring_mul_1_l.
  - now rewrite IHx, ring_mul_assoc.
  - now rewrite ring_mul_1_l.
 Qed.

(*morphisms are extensionally equal*)
 Lemma same_genZ : forall x, [x] == gen_phiZ1 x.
 Proof.
  destruct x;rsimpl; try rewrite same_gen; reflexivity.
 Qed.

 Lemma gen_phiZ1_add_pos_neg : forall x y,
 gen_phiZ1 (Z.pos_sub x y)
 == gen_phiPOS1 x + -gen_phiPOS1 y.
 Proof.
  intros x y.
  generalize (Z.pos_sub_discr x y).
  destruct (Z.pos_sub x y) as [|p|p]; intros; subst.
  - now rewrite ring_opp_def.
  - rewrite ARgen_phiPOS_add; simpl.
    add_push (gen_phiPOS1 p). now rewrite ring_opp_def, ring_add_0_l.
  - rewrite ARgen_phiPOS_add; simpl.
    now rewrite ring_opp_add, ring_add_assoc, ring_opp_def, ring_add_0_l.
 Qed.

 Lemma match_compOpp : forall x (B:Type) (be bl bg:B),
  match CompOpp x with Eq => be | Lt => bl | Gt => bg end
  = match x with Eq => be | Lt => bg | Gt => bl end.
 Proof. destruct x;simpl;intros;trivial. Qed.

 Lemma gen_phiZ_add : forall x y, [x + y] == [x] + [y].
 Proof.
  intros x y; repeat rewrite same_genZ; generalize x y;clear x y.
  induction x;destruct y;simpl;norm.
  - apply ARgen_phiPOS_add.
  - apply gen_phiZ1_add_pos_neg.
  - rewrite gen_phiZ1_add_pos_neg. rewrite ring_add_comm.
    reflexivity.
  - rewrite ARgen_phiPOS_add. rewrite ring_opp_add. reflexivity.
 Qed.

Lemma gen_phiZ_opp : forall x, [- x] == - [x].
 Proof.
  intros x. repeat rewrite same_genZ. generalize x ;clear x.
  induction x;simpl;norm.
  rewrite ring_opp_opp.  reflexivity.
 Qed.

 Lemma gen_phiZ_mul : forall x y, [x * y] == [x] * [y].
 Proof.
  intros x y;repeat rewrite same_genZ.
  destruct x; simpl; [now rewrite ring_mul_0_l|destruct y..]; simpl.
  - now rewrite ring_mul_0_r.
  - now rewrite ARgen_phiPOS_mult.
  - now rewrite ARgen_phiPOS_mult, ring_opp_mul_r.
  - now rewrite ring_mul_0_r.
  - now rewrite ARgen_phiPOS_mult, ring_opp_mul_l.
  - now rewrite ARgen_phiPOS_mult, <- ring_opp_mul_l, <- ring_opp_mul_r, ring_opp_opp.
 Qed.

 Lemma gen_phiZ_ext : forall x y : Z, x = y -> [x] == [y].
 Proof. intros;subst;reflexivity. Qed.

Declare Equivalent Keys bracket gen_phiZ.
(*proof that [.] satisfies morphism specifications*)
Global Instance gen_phiZ_morph :
(@Ring_morphism (Z:Type) R _ _ _ _ _ _ _ Zops Zr _ _ _ _ _ _ _ _ _ gen_phiZ) . (* beurk!*)
 apply Build_Ring_morphism; simpl;try reflexivity.
- apply gen_phiZ_add.
- intros. rewrite ring_sub_def.
  replace (x-y)%Z with (x + (-y))%Z.
  + now rewrite gen_phiZ_add, gen_phiZ_opp, ring_sub_def.
  + reflexivity.
- apply gen_phiZ_mul.
- apply gen_phiZ_opp.
- apply gen_phiZ_ext.
Defined.

#[deprecated(since="9.0")]
Lemma gen_Zeqb_ok : forall x y,
  Z.eqb x y = true -> [x] == [y].
Proof. intros x y ->%Z.eqb_eq; reflexivity. Qed.

End ZMORPHISM.

#[global]
Instance multiplication_phi_ring{R:Type}`{Ring R} : Multiplication  :=
  {multiplication x y := (gen_phiZ x) * y}.

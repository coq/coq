(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
Require Import Bool ZArith.
Require Import ZifyClasses.
Local Open Scope Z_scope.
(* Instances of [ZifyClasses] for dealing with boolean operators.
   Various encodings of boolean are possible.  One objective is to
   have an encoding that is terse but also lia friendly.
 *)

(** [Z_of_bool] is the injection function for boolean *)
Definition Z_of_bool (b : bool) : Z := if b then 1 else 0.

(** [bool_of_Z] is a compatible reverse operation *)
Definition bool_of_Z (z : Z) : bool := negb (Z.eqb z 0).

Lemma Z_of_bool_bound : forall x,   0 <= Z_of_bool x <= 1.
Proof.
  destruct x ; simpl; compute; intuition congruence.
Qed.

Instance Inj_bool_Z : InjTyp bool Z :=
  { inj := Z_of_bool ; pred :=(fun x => 0 <= x <= 1) ; cstr := Z_of_bool_bound}.
Add InjTyp Inj_bool_Z.

(** Boolean operators *)

Instance Op_andb : BinOp andb :=
  { TBOp := Z.min ;
    TBOpInj := ltac: (destruct n,m; reflexivity)}.
Add BinOp Op_andb.

Instance Op_orb : BinOp orb :=
  { TBOp := Z.max ;
    TBOpInj := ltac:(destruct n,m; reflexivity)}.
Add BinOp Op_orb.

Instance Op_negb : UnOp negb :=
  { TUOp := fun x => 1 - x ; TUOpInj := ltac:(destruct x; reflexivity)}.
Add UnOp Op_negb.

Instance Op_eq_bool : BinRel (@eq bool) :=
  {TR := @eq Z ; TRInj := ltac:(destruct n,m; simpl ; intuition congruence) }.
Add BinRel Op_eq_bool.

Instance Op_true : CstOp true :=
  { TCst := 1 ; TCstInj := eq_refl }.
Add CstOp Op_true.

Instance Op_false : CstOp false :=
  { TCst := 0 ; TCstInj := eq_refl }.
Add CstOp Op_false.

(** Comparisons are encoded using the predicates [isZero] and [isLeZero].*)

Definition isZero (z : Z) := Z_of_bool (Z.eqb z 0).

Definition isLeZero (x : Z) := Z_of_bool (Z.leb x 0).

(* Some intermediate lemma *)

Lemma Z_eqb_isZero : forall n m,
    Z_of_bool (n =? m) = isZero (n - m).
Proof.
  intros ; unfold isZero.
  destruct ( n =? m) eqn:EQ.
  - simpl. rewrite Z.eqb_eq in EQ.
    rewrite EQ. rewrite Z.sub_diag.
    reflexivity.
  -
    destruct (n - m =? 0) eqn:EQ'.
    rewrite Z.eqb_neq in EQ.
    rewrite Z.eqb_eq in EQ'.
    apply Zminus_eq in EQ'.
    congruence.
    reflexivity.
Qed.

Lemma Z_leb_sub : forall x y, x <=? y  = ((x - y) <=? 0).
Proof.
  intros.
  destruct (x <=?y) eqn:B1 ;
    destruct (x - y <=?0) eqn:B2 ; auto.
  - rewrite Z.leb_le in B1.
    rewrite Z.leb_nle in B2.
    rewrite Z.le_sub_0 in B2. tauto.
  - rewrite Z.leb_nle in B1.
    rewrite Z.leb_le in B2.
    rewrite Z.le_sub_0 in B2. tauto.
Qed.

Lemma Z_ltb_leb : forall x y, x <? y  = (x +1 <=? y).
Proof.
  intros.
  destruct (x <?y) eqn:B1 ;
    destruct (x + 1 <=?y) eqn:B2 ; auto.
  - rewrite Z.ltb_lt in B1.
    rewrite Z.leb_nle in B2.
    apply Zorder.Zlt_le_succ in B1.
    unfold Z.succ in B1.
    tauto.
  - rewrite Z.ltb_nlt in B1.
    rewrite Z.leb_le in B2.
    apply Zorder.Zle_lt_succ in B2.
    unfold Z.succ in B2.
    apply Zorder.Zplus_lt_reg_r in B2.
    tauto.
Qed.


(** Comparison over Z *)

Instance Op_Zeqb : BinOp Z.eqb :=
  { TBOp := fun x y => isZero (Z.sub x y) ; TBOpInj := Z_eqb_isZero}.

Instance Op_Zleb : BinOp Z.leb :=
  { TBOp := fun x y => isLeZero (x-y) ;
    TBOpInj :=
      ltac: (intros;unfold isLeZero;
               rewrite Z_leb_sub;
               auto) }.
Add BinOp Op_Zleb.

Instance Op_Zgeb : BinOp Z.geb :=
  { TBOp := fun x y => isLeZero (y-x) ;
    TBOpInj := ltac:(
                 intros;
                   unfold isLeZero;
                   rewrite Z.geb_leb;
                   rewrite Z_leb_sub;
                   auto) }.
Add BinOp Op_Zgeb.

Instance Op_Zltb : BinOp Z.ltb :=
  { TBOp := fun x y => isLeZero (x+1-y) ;
    TBOpInj := ltac:(
                 intros;
                   unfold isLeZero;
                   rewrite Z_ltb_leb;
                   rewrite <- Z_leb_sub;
                   reflexivity) }.

Instance Op_Zgtb : BinOp Z.gtb :=
  { TBOp := fun x y => isLeZero (y-x+1) ;
    TBOpInj := ltac:(
                 intros;
                   unfold isLeZero;
                   rewrite Z.gtb_ltb;
                   rewrite Z_ltb_leb;
                   rewrite Z_leb_sub;
                   rewrite Z.add_sub_swap;
                   reflexivity) }.
Add BinOp Op_Zgtb.

(** Comparison over nat *)


Lemma Z_of_nat_eqb_iff : forall n m,
    (n =? m)%nat = (Z.of_nat n =? Z.of_nat m).
Proof.
  intros.
  rewrite Nat.eqb_compare.
  rewrite Z.eqb_compare.
  rewrite Nat2Z.inj_compare.
  reflexivity.
Qed.

Lemma Z_of_nat_leb_iff : forall n m,
    (n <=? m)%nat = (Z.of_nat n <=? Z.of_nat m).
Proof.
  intros.
  rewrite Nat.leb_compare.
  rewrite Z.leb_compare.
  rewrite Nat2Z.inj_compare.
  reflexivity.
Qed.

Lemma Z_of_nat_ltb_iff : forall n m,
    (n <? m)%nat = (Z.of_nat n <? Z.of_nat m).
Proof.
  intros.
  rewrite Nat.ltb_compare.
  rewrite Z.ltb_compare.
  rewrite Nat2Z.inj_compare.
  reflexivity.
Qed.

Instance Op_nat_eqb : BinOp Nat.eqb :=
   { TBOp := fun x y => isZero (Z.sub x y) ;
     TBOpInj := ltac:(
                  intros; simpl;
                    rewrite  <- Z_eqb_isZero;
                  f_equal; apply Z_of_nat_eqb_iff) }.
Add BinOp Op_nat_eqb.

Instance Op_nat_leb : BinOp Nat.leb :=
  { TBOp := fun x y => isLeZero (x-y) ;
    TBOpInj := ltac:(
                 intros;
                 rewrite Z_of_nat_leb_iff;
                 unfold isLeZero;
                 rewrite Z_leb_sub;
                 auto) }.
Add BinOp Op_nat_leb.

Instance Op_nat_ltb : BinOp Nat.ltb :=
  { TBOp := fun x y => isLeZero (x+1-y) ;
     TBOpInj := ltac:(
                  intros;
                  rewrite Z_of_nat_ltb_iff;
                    unfold isLeZero;
                    rewrite Z_ltb_leb;
                    rewrite <- Z_leb_sub;
                    reflexivity) }.
Add BinOp Op_nat_ltb.

(** Injected boolean operators *)

Lemma Z_eqb_ZSpec_ok : forall x,  0 <= isZero x <= 1 /\
                                  (x = 0 <-> isZero x = 1).
Proof.
  intros.
  unfold isZero.
  destruct (x =? 0) eqn:EQ.
  -  apply Z.eqb_eq in EQ.
     simpl. intuition try congruence;
     compute ; congruence.
  - apply Z.eqb_neq in EQ.
    simpl. intuition try congruence;
             compute ; congruence.
Qed.


Instance Z_eqb_ZSpec : UnOpSpec isZero :=
  {| UPred := fun n r => 0 <= r <= 1 /\ (n = 0 <-> isZero n = 1) ; USpec := Z_eqb_ZSpec_ok |}.
Add Spec Z_eqb_ZSpec.

Lemma leZeroSpec_ok : forall x,  x <= 0 /\ isLeZero x = 1 \/ x > 0 /\ isLeZero x = 0.
Proof.
  intros.
  unfold isLeZero.
  destruct (x <=? 0) eqn:EQ.
  -  apply Z.leb_le in EQ.
     simpl. intuition congruence.
  -  simpl.
     apply Z.leb_nle in EQ.
     apply Zorder.Znot_le_gt in EQ.
     tauto.
Qed.

Instance leZeroSpec : UnOpSpec isLeZero :=
  {| UPred := fun n r => (n<=0 /\ r = 1) \/ (n > 0 /\ r = 0) ; USpec := leZeroSpec_ok|}.
Add Spec leZeroSpec.

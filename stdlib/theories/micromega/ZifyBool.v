(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
Require Import Bool ZArith.
Require Import Zify ZifyClasses.
Require Import ZifyInst.
Local Open Scope Z_scope.
(* Instances of [ZifyClasses] for dealing with boolean operators. *)

#[global]
Instance Inj_bool_bool : InjTyp bool bool :=
  { inj b := b ; pred b := b = true \/ b = false ;
    cstr b := ltac:(destruct b; tauto) }.
Add Zify InjTyp Inj_bool_bool.

(** Boolean operators *)

#[global]
Instance Op_andb : BinOp andb :=
  { TBOp := andb ; TBOpInj _ _ := eq_refl}.
Add Zify BinOp Op_andb.

#[global]
Instance Op_orb : BinOp orb :=
  { TBOp := orb ; TBOpInj _ _ := eq_refl}.
Add Zify BinOp Op_orb.

#[global]
Instance Op_implb : BinOp implb :=
  { TBOp := implb; TBOpInj _ _ := eq_refl }.
Add Zify BinOp Op_implb.

Lemma xorb_eq b1 b2 : xorb b1 b2 = andb (orb b1 b2) (negb (eqb b1 b2)).
Proof.
  destruct b1, b2 ; reflexivity.
Qed.

#[global]
Instance Op_xorb : BinOp xorb :=
  { TBOp x y := andb (orb x y) (negb (eqb x y)); TBOpInj := xorb_eq }.
Add Zify BinOp Op_xorb.

#[global]
Instance Op_eqb : BinOp eqb :=
  { TBOp := eqb; TBOpInj _ _ := eq_refl }.
Add Zify BinOp Op_eqb.

#[global]
Instance Op_negb : UnOp negb :=
  { TUOp := negb ; TUOpInj _ := eq_refl}.
Add Zify UnOp Op_negb.

#[global]
Instance Op_eq_bool : BinRel (@eq bool) :=
  {TR := @eq bool ; TRInj b1 b2 := iff_refl (b1 = b2) }.
Add Zify BinRel Op_eq_bool.

#[global]
Instance Op_true : CstOp true :=
  { TCst := true ; TCstInj := eq_refl }.
Add Zify CstOp Op_true.

#[global]
Instance Op_false : CstOp false :=
  { TCst := false ; TCstInj := eq_refl }.
Add Zify CstOp Op_false.

(** Comparison over Z *)

#[global]
Instance Op_Zeqb : BinOp Z.eqb :=
  { TBOp := Z.eqb ; TBOpInj _ _ := eq_refl }.
Add Zify BinOp Op_Zeqb.

#[global]
Instance Op_Zleb : BinOp Z.leb :=
  { TBOp := Z.leb; TBOpInj _ _ := eq_refl }.
Add Zify BinOp Op_Zleb.

#[global]
Instance Op_Zgeb : BinOp Z.geb :=
  { TBOp := Z.geb; TBOpInj _ _ := eq_refl }.
Add Zify BinOp Op_Zgeb.

#[global]
Instance Op_Zltb : BinOp Z.ltb :=
  { TBOp := Z.ltb ; TBOpInj _ _ := eq_refl }.
Add Zify BinOp Op_Zltb.

#[global]
Instance Op_Zgtb : BinOp Z.gtb :=
  { TBOp := Z.gtb; TBOpInj _ _ := eq_refl }.
Add Zify BinOp Op_Zgtb.

(** Comparison over N *)

#[global]
Instance Op_Neqb : BinOp N.eqb :=
  { TBOp := Z.eqb; TBOpInj n m := ltac:(now destruct n, m) }.
Add Zify BinOp Op_Neqb.

#[global]
Instance Op_Nleb : BinOp N.leb :=
  { TBOp := Z.leb; TBOpInj n m := ltac:(now destruct n, m) }.
Add Zify BinOp Op_Nleb.

#[global]
Instance Op_Nltb : BinOp N.ltb :=
  { TBOp := Z.ltb; TBOpInj n m := ltac:(now destruct n, m) }.
Add Zify BinOp Op_Nltb.

(** Comparison over positive *)

#[global]
Instance Op_Pos_eqb : BinOp Pos.eqb :=
  { TBOp := Z.eqb; TBOpInj _ _ := eq_refl }.
Add Zify BinOp Op_Pos_eqb.

#[global]
Instance Op_Pos_leb : BinOp Pos.leb :=
  { TBOp := Z.leb; TBOpInj _ _ := eq_refl }.
Add Zify BinOp Op_Pos_leb.

#[global]
Instance Op_Pos_ltb : BinOp Pos.ltb :=
  { TBOp := Z.ltb; TBOpInj _ _ := eq_refl }.
Add Zify BinOp Op_Pos_ltb.

(** Comparison over nat *)

Lemma Z_of_nat_eqb_iff n m : (n =? m)%nat = (Z.of_nat n =? Z.of_nat m).
Proof.
  rewrite Nat.eqb_compare.
  rewrite Z.eqb_compare.
  rewrite Nat2Z.inj_compare.
  reflexivity.
Qed.

Lemma Z_of_nat_leb_iff n m : (n <=? m)%nat = (Z.of_nat n <=? Z.of_nat m).
Proof.
  rewrite Nat.leb_compare.
  rewrite Z.leb_compare.
  rewrite Nat2Z.inj_compare.
  reflexivity.
Qed.

Lemma Z_of_nat_ltb_iff n m : (n <? m)%nat = (Z.of_nat n <? Z.of_nat m).
Proof.
  rewrite Nat.ltb_compare.
  rewrite Z.ltb_compare.
  rewrite Nat2Z.inj_compare.
  reflexivity.
Qed.

#[global]
Instance Op_nat_eqb : BinOp Nat.eqb :=
  { TBOp := Z.eqb; TBOpInj := Z_of_nat_eqb_iff }.
Add Zify BinOp Op_nat_eqb.

#[global]
Instance Op_nat_leb : BinOp Nat.leb :=
  { TBOp := Z.leb; TBOpInj := Z_of_nat_leb_iff }.
Add Zify BinOp Op_nat_leb.

#[global]
Instance Op_nat_ltb : BinOp Nat.ltb :=
  { TBOp := Z.ltb; TBOpInj := Z_of_nat_ltb_iff }.
Add Zify BinOp Op_nat_ltb.

Lemma b2n_b2z x : Z.of_nat (Nat.b2n x) = Z.b2z x.
Proof.
destruct x ; reflexivity.
Qed.

#[global]
Instance Op_b2n : UnOp Nat.b2n :=
  { TUOp := Z.b2z; TUOpInj := b2n_b2z }.
Add Zify UnOp Op_b2n.

#[global]
Instance Op_b2z : UnOp Z.b2z :=
  { TUOp := Z.b2z; TUOpInj _ := eq_refl }.
Add Zify UnOp Op_b2z.

Lemma b2z_spec b : (b = true /\ Z.b2z b = 1) \/ (b = false /\ Z.b2z b = 0).
Proof.
  destruct b ; simpl; tauto.
Qed.

#[global]
Instance b2zSpec : UnOpSpec Z.b2z :=
  { UPred b r := (b = true /\ r = 1) \/ (b = false /\ r = 0);
    USpec := b2z_spec }.
Add Zify UnOpSpec b2zSpec.

Ltac elim_bool_cstr :=
  repeat match goal with
         | C : ?B = true \/ ?B = false |- _ =>
           destruct C as [C|C]; rewrite C in *
         end.

Ltac Zify.zify_post_hook ::= elim_bool_cstr.

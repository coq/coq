(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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

Instance Inj_bool_bool : InjTyp bool bool :=
  { inj := (fun x => x) ; pred := (fun b => b = true \/ b = false) ;
    cstr := (ltac:(intro b; destruct b; tauto))}.
Add Zify InjTyp Inj_bool_bool.

(** Boolean operators *)

Instance Op_andb : BinOp andb :=
  { TBOp := andb ; TBOpInj := fun _ _  => eq_refl}.
Add Zify BinOp Op_andb.

Instance Op_orb : BinOp orb :=
  { TBOp := orb ; TBOpInj := fun _ _ => eq_refl}.
Add Zify BinOp Op_orb.

Instance Op_implb : BinOp implb :=
  { TBOp := implb; TBOpInj := fun _ _ => eq_refl }.
Add Zify BinOp Op_implb.

Definition xorb_eq : forall b1 b2,
    xorb b1 b2 = andb (orb b1 b2) (negb (eqb b1 b2)).
Proof.
  destruct b1,b2 ; reflexivity.
Qed.

Instance Op_xorb : BinOp xorb :=
  { TBOp := fun x y => andb (orb x y) (negb (eqb x y)); TBOpInj := xorb_eq }.
Add Zify BinOp Op_xorb.

Instance Op_eqb : BinOp eqb :=
  { TBOp := eqb; TBOpInj := fun _ _ => eq_refl }.
Add Zify BinOp Op_eqb.

Instance Op_negb : UnOp negb :=
  { TUOp := negb ; TUOpInj := fun _ => eq_refl}.
Add Zify UnOp Op_negb.

Instance Op_eq_bool : BinRel (@eq bool) :=
  {TR := @eq bool ; TRInj := ltac:(reflexivity) }.
Add Zify BinRel Op_eq_bool.

Instance Op_true : CstOp true :=
  { TCst := true ; TCstInj := eq_refl }.
Add Zify CstOp Op_true.

Instance Op_false : CstOp false :=
  { TCst := false ; TCstInj := eq_refl }.
Add Zify CstOp Op_false.

(** Comparison over Z *)

Instance Op_Zeqb : BinOp Z.eqb :=
  { TBOp := Z.eqb ; TBOpInj := fun _ _ => eq_refl }.
Add Zify BinOp Op_Zeqb.

Instance Op_Zleb : BinOp Z.leb :=
  { TBOp := Z.leb; TBOpInj :=  fun _ _ => eq_refl }.
Add Zify BinOp Op_Zleb.

Instance Op_Zgeb : BinOp Z.geb :=
  { TBOp := Z.geb; TBOpInj := fun _ _ => eq_refl }.
Add Zify BinOp Op_Zgeb.

Instance Op_Zltb : BinOp Z.ltb :=
  { TBOp := Z.ltb ; TBOpInj := fun _ _ => eq_refl }.
Add Zify BinOp Op_Zltb.

Instance Op_Zgtb : BinOp Z.gtb :=
  { TBOp := Z.gtb; TBOpInj := fun _ _  => eq_refl }.
Add Zify BinOp Op_Zgtb.

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
  { TBOp := Z.eqb; TBOpInj := Z_of_nat_eqb_iff }.
Add Zify BinOp Op_nat_eqb.

Instance Op_nat_leb : BinOp Nat.leb :=
  { TBOp := Z.leb; TBOpInj := Z_of_nat_leb_iff }.
Add Zify BinOp Op_nat_leb.

Instance Op_nat_ltb : BinOp Nat.ltb :=
  { TBOp := Z.ltb; TBOpInj := Z_of_nat_ltb_iff }.
Add Zify BinOp Op_nat_ltb.

Lemma b2n_b2z :  forall x,  Z.of_nat (Nat.b2n x) = Z.b2z x.
Proof.
  intro. destruct x ; reflexivity.
Qed.

Instance Op_b2n : UnOp Nat.b2n :=
  { TUOp := Z.b2z; TUOpInj := b2n_b2z }.
Add Zify UnOp Op_b2n.

Instance Op_b2z : UnOp Z.b2z :=
  { TUOp := Z.b2z; TUOpInj := fun _ => eq_refl }.
Add Zify UnOp Op_b2z.

Lemma b2z_spec : forall b, (b = true /\ Z.b2z b = 1) \/ (b = false /\ Z.b2z b = 0).
Proof.
  destruct b ; simpl; intuition congruence.
Qed.

Instance b2zSpec : UnOpSpec Z.b2z :=
  { UPred := fun b r => (b = true /\ r = 1) \/ (b = false /\ r = 0);
    USpec := b2z_spec
  }.
Add Zify UnOpSpec b2zSpec.

Ltac elim_bool_cstr :=
  repeat match goal with
         | C : ?B = true \/ ?B = false |- _ =>
           destruct C as [C|C]; rewrite C in *
         end.

Ltac Zify.zify_post_hook ::= elim_bool_cstr.

(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
(****************************************************************************)
(*                                                                          *)
(*                         Naive Set Theory in Coq                          *)
(*                                                                          *)
(*                     INRIA                        INRIA                   *)
(*              Rocquencourt                        Sophia-Antipolis        *)
(*                                                                          *)
(*                                 Coq V6.1                                 *)
(*									    *)
(*			         Gilles Kahn 				    *)
(*				 Gerard Huet				    *)
(*									    *)
(*									    *)
(*                                                                          *)
(* Acknowledgments: This work was started in July 1993 by F. Prost. Thanks  *)
(* to the Newton Institute for providing an exceptional work environment    *)
(* in Summer 1995. Several developments by E. Ledinot were an inspiration.  *)
(****************************************************************************)

(* $Id$ *)

Require Export Finite_sets.
Require Export Constructive_sets.
Require Export Classical_Type.
Require Export Classical_sets.
Require Export Powerset.
Require Export Powerset_facts.
Require Export Powerset_Classical_facts.
Require Export Gt.
Require Export Lt.
Require Export Le.
Require Export Finite_sets_facts.
Require Export Image.
Require Export Infinite_sets.
Require Export Compare_dec.
Require Export Relations_1.
Require Export Partial_Order.
Require Export Cpo.

Section Integers_sect.

Inductive Nat : Type :=
      mkNat: nat -> Nat.

Parameter nat_of_Nat: Nat -> nat.

Axiom nat_of_nat_returns: (n: nat) (nat_of_Nat (mkNat n)) = n.

Lemma mkNat_injective: (n1, n2: nat) (mkNat n1) == (mkNat n2) -> n1 = n2.
Proof.
Intros n1 n2 H'; Try Assumption.
Rewrite <- (nat_of_nat_returns n1).
Rewrite <- (nat_of_nat_returns n2).
Rewrite H'; Auto with sets arith.
Qed.

Inductive Integers : (Ensemble Nat) :=
      Integers_defn: (x: Nat) (In Nat Integers x).
Hints Resolve Integers_defn.

Inductive Le_Nat [x, y:Nat]: Prop :=
      Definition_of_Le_nat:
        (n1, n2: nat) x == (mkNat n1) -> y == (mkNat n2) -> (le n1 n2) ->
         (Le_Nat x y).

Lemma Le_Nat_direct: (n1, n2: nat) (le n1 n2) -> (Le_Nat (mkNat n1) (mkNat n2)).
Proof.
Intros n1 n2 H'.
Apply Definition_of_Le_nat with n1 := n1 n2 := n2; Auto with sets arith.
Qed.
Hints Resolve Le_Nat_direct.

Lemma Le_Nat_Reflexive: (Reflexive Nat Le_Nat).
Proof.
Red.
Intro x; Elim x; Auto with sets arith.
Qed.
Hints Resolve Le_Nat_Reflexive.

Lemma Le_Nat_antisym: (Antisymmetric Nat Le_Nat).
Proof.
Red.
Intros x y H'; Elim H'.
Intros n1 n2 H'0 H'1 H'2 H'3; Elim H'3.
Intros n3 n4 H'4 H'5 H'6.
Cut n1 = n4 /\ n2 = n3.
Intro H'7.
Generalize H'6.
Elim H'7; Intros H'8 H'9; Rewrite <- H'8; Clear H'7.
Rewrite <- H'9.
Intro H'7.
Cut n1 = n2.
Rewrite H'0; Rewrite H'1.
Intro H'10; Rewrite <- H'10; Auto with sets arith.
Apply le_antisym; Auto with sets arith.
Split; Apply mkNat_injective.
Rewrite <- H'5; Rewrite H'0; Auto with sets arith.
Rewrite <- H'4; Rewrite H'1; Auto with sets arith.
Qed.

Hints Resolve Le_Nat_antisym.

Lemma Le_Nat_trans: (Transitive Nat Le_Nat).
Proof.
Red.
Intros x y z H'; Elim H'.
Intros n1 n2 H'0 H'1 H'2 H'3; Elim H'3.
Intros n3 n4 H'4 H'5 H'6.
Rewrite H'0; Rewrite H'5.
Apply Le_Nat_direct.
Apply le_trans with m := n3; Auto with sets arith.
Cut n2 = n3.
Intro H'7; Rewrite <- H'7; Auto with sets arith.
Apply mkNat_injective.
Rewrite <- H'4; Rewrite <- H'1; Auto with sets arith.
Qed.
Hints Resolve Le_Nat_trans.

Lemma Le_Nat_Order: (Order Nat Le_Nat).
Proof.
Auto with sets arith.
Qed.
Hints Resolve Le_Nat_Order.

Definition Nat_O :=  (mkNat O).

Lemma triv_Nat: (n: nat) (In Nat Integers (mkNat n)).
Proof.
Auto with sets arith.
Qed.
Hints Resolve triv_Nat.

Definition Nat_po: (PO Nat).
Apply Definition_of_PO with Carrier_of := Integers Rel_of := Le_Nat; Auto with sets arith.
Apply Inhabited_intro with x := Nat_O; Auto with sets arith.
Defined.
Hints Unfold  Nat_po.

Lemma Le_Nat_total_order: (Totally_ordered Nat Nat_po Integers).
Proof.
Apply Totally_ordered_definition.
Simpl.
Intros H' x; Elim x.
Intros n y; Elim y.
Intros n0 H'0.
Specialize 2 le_or_lt with n := n m := n0; Intro H'2; Elim H'2.
Intro H'1; Left; Auto with sets arith.
Intro H'1; Right.
Cut (le n0 n); Auto with sets arith.
Qed.
Hints Resolve Le_Nat_total_order.

Lemma Finite_subset_has_lub:
  (X: (Ensemble Nat)) (Finite Nat X) ->
   (EXT m: Nat | (Upper_Bound Nat Nat_po X m)).
Proof.
Intros X H'; Elim H'.
Exists Nat_O.
Apply Upper_Bound_definition; Auto with sets arith.
Intros y H'0; Elim H'0; Auto with sets arith.
Intros A H'0 H'1 x H'2; Try Assumption.
Elim H'1; Intros x0 H'3; Clear H'1.
Elim Le_Nat_total_order.
Simpl.
Intro H'1; Try Assumption.
LApply H'1; [Intro H'4; Idtac | Try Assumption]; Auto with sets arith.
Generalize (H'4 x0 x).
Clear H'4.
Clear H'1.
Intro H'1; LApply H'1;
 [Intro H'4; Elim H'4;
   [Intro H'5; Try Exact H'5; Clear H'4 H'1 | Intro H'5; Clear H'4 H'1] |
   Clear H'1].
Exists x.
Apply Upper_Bound_definition; Auto with sets arith; Simpl.
Intros y H'1; Elim H'1.
Generalize Le_Nat_trans.
Intro H'4; Red in H'4.
Intros x1 H'6; Try Assumption.
Apply H'4 with y := x0; Auto with sets arith.
Elim H'3; Simpl; Auto with sets arith.
Intros x1 H'4; Elim H'4; Auto with sets arith.
Exists x0.
Apply Upper_Bound_definition; Auto with sets arith; Simpl.
Intros y H'1; Elim H'1.
Intros x1 H'4; Try Assumption.
Elim H'3; Simpl; Auto with sets arith.
Intros x1 H'4; Elim H'4; Auto with sets arith.
Red.
Intros x1 H'1; Elim H'1; Auto with sets arith.
Qed.

Lemma Integers_has_no_ub: ~ (EXT m:Nat | (Upper_Bound Nat Nat_po Integers m)).
Proof.
Red; Intro H'; Elim H'.
Intro x; Elim x.
Intros n H'0; Elim H'0.
Intros H'1 H'2; Try Assumption.
Cut (In Nat Integers (mkNat (S n))).
Intro H'3; Try Assumption.
Specialize 1 H'2 with y := (mkNat (S n)); Intro H'4; LApply H'4;
 [Intro H'5; Clear H'4 | Try Assumption; Clear H'4].
Simpl in H'5.
Elim H'5.
Intros n1 n2 H'4 H'6; Try Assumption.
Specialize 2 mkNat_injective with n1 := (S n) n2 := n1; Intro H'8; LApply H'8;
 [Intro H'9; Rewrite <- H'9; Clear H'8 | Clear H'8]; Auto with sets arith.
Specialize 2 mkNat_injective with n1 := n n2 := n2; Intro H'8; LApply H'8;
 [Intro H'10; Rewrite <- H'10; Clear H'8 | Clear H'8]; Auto with sets arith.
Intro H'7; Try Assumption.
Specialize 1 le_Sn_n with n := n; Intro H'8; Elim H'8.
Auto with sets arith.
Auto with sets arith.
Qed.

Lemma Integers_infinite: ~ (Finite Nat Integers).
Proof.
Generalize Integers_has_no_ub.
Intro H'; Red; Intro H'0; Try Exact H'0.
Apply H'.
Apply Finite_subset_has_lub; Auto with sets arith.
Qed.

End Integers_sect.

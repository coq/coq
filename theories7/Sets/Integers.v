(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
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

(*i $Id$ i*)

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

Inductive Integers : (Ensemble nat) :=
      Integers_defn: (x: nat) (In nat Integers x).
Hints Resolve Integers_defn.

Lemma le_reflexive: (Reflexive nat le).
Proof.
Red; Auto with arith.
Qed.

Lemma le_antisym: (Antisymmetric nat le).
Proof.
Red; Intros x y H H';Rewrite (le_antisym x y);Auto.
Qed.

Lemma le_trans: (Transitive nat le).
Proof.
Red; Intros; Apply le_trans with y;Auto.
Qed.
Hints Resolve le_reflexive le_antisym le_trans.

Lemma le_Order: (Order nat le).
Proof.
Auto with sets arith.
Qed.
Hints Resolve le_Order.

Lemma triv_nat: (n: nat) (In nat Integers n).
Proof.
Auto with sets arith.
Qed.
Hints Resolve triv_nat.

Definition nat_po: (PO nat).
Apply Definition_of_PO with Carrier_of := Integers Rel_of := le; Auto with sets arith.
Apply Inhabited_intro with x := O; Auto with sets arith.
Defined.
Hints Unfold nat_po.

Lemma le_total_order: (Totally_ordered nat nat_po Integers).
Proof.
Apply Totally_ordered_definition.
Simpl.
Intros H' x y H'0.
Specialize 2 le_or_lt with n := x m := y; Intro H'2; Elim H'2.
Intro H'1; Left; Auto with sets arith.
Intro H'1; Right.
Cut (le y x); Auto with sets arith.
Qed.
Hints Resolve le_total_order.

Lemma Finite_subset_has_lub:
  (X: (Ensemble nat)) (Finite nat X) ->
   (EXT m: nat | (Upper_Bound nat nat_po X m)).
Proof.
Intros X H'; Elim H'.
Exists O.
Apply Upper_Bound_definition; Auto with sets arith.
Intros y H'0; Elim H'0; Auto with sets arith.
Intros A H'0 H'1 x H'2; Try Assumption.
Elim H'1; Intros x0 H'3; Clear H'1.
Elim le_total_order.
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
Generalize le_trans.
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

Lemma Integers_has_no_ub: ~ (EXT m:nat | (Upper_Bound nat nat_po Integers m)).
Proof.
Red; Intro H'; Elim H'.
Intros x H'0.
Elim H'0; Intros H'1 H'2.
Cut (In nat Integers (S x)).
Intro H'3.
Specialize 1 H'2 with y := (S x); Intro H'4; LApply H'4;
 [Intro H'5; Clear H'4 | Try Assumption; Clear H'4].
Simpl in H'5.
Absurd (le (S x) x); Auto with arith.
Auto with sets arith.
Qed.

Lemma Integers_infinite: ~ (Finite nat Integers).
Proof.
Generalize Integers_has_no_ub.
Intro H'; Red; Intro H'0; Try Exact H'0.
Apply H'.
Apply Finite_subset_has_lub; Auto with sets arith.
Qed.

End Integers_sect.






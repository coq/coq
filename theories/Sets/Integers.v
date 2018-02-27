(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
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

Require Export Finite_sets.
Require Export Constructive_sets.
Require Export Classical.
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

  Inductive Integers : Ensemble nat :=
    Integers_defn : forall x:nat, In nat Integers x.

  Lemma le_reflexive : Reflexive nat le.
  Proof.
    red; auto with arith.
  Qed.

  Lemma le_antisym : Antisymmetric nat le.
  Proof.
    red; intros x y H H'; rewrite (le_antisym x y); auto.
  Qed.

  Lemma le_trans : Transitive nat le.
  Proof.
    red; intros; apply le_trans with y; auto.
  Qed.

  Lemma le_Order : Order nat le.
  Proof.
    split; [exact le_reflexive | exact le_trans | exact le_antisym].
  Qed.

  Lemma triv_nat : forall n:nat, In nat Integers n.
  Proof.
    exact Integers_defn.
  Qed.

  Definition nat_po : PO nat.
    apply Definition_of_PO with (Carrier_of := Integers) (Rel_of := le);
      auto with sets arith.
    apply Inhabited_intro with (x := 0).
      apply Integers_defn.
    exact le_Order.
  Defined.

  Lemma le_total_order : Totally_ordered nat nat_po Integers.
  Proof.
    apply Totally_ordered_definition.
    simpl.
    intros H' x y H'0.
    elim le_or_lt with (n := x) (m := y).
    intro H'1; left; auto with sets arith.
    intro H'1; right.
    cut (y <= x); auto with sets arith.
  Qed.

  Lemma Finite_subset_has_lub :
    forall X:Ensemble nat,
      Finite nat X ->  exists m : nat, Upper_Bound nat nat_po X m.
  Proof.
    intros X H'; elim H'.
    exists 0.
    apply Upper_Bound_definition.
      unfold nat_po. simpl. apply triv_nat.
    intros y H'0; elim H'0; auto with sets arith.
    intros A H'0 H'1 x H'2; try assumption.
    elim H'1; intros x0 H'3; clear H'1.
    elim le_total_order.
    simpl.
    intro H'1; try assumption.
    lapply H'1; [ intro H'4; idtac | try assumption ]; auto with sets arith.
    generalize (H'4 x0 x).
    clear H'4.
    clear H'1.
    intro H'1; lapply H'1;
      [ intro H'4; elim H'4;
	[ intro H'5; try exact H'5; clear H'4 H'1 | intro H'5; clear H'4 H'1 ]
	| clear H'1 ].
    exists x.
    apply Upper_Bound_definition. simpl. apply triv_nat.
    intros y H'1; elim H'1.
    generalize le_trans.
    intro H'4; red in H'4.
    intros x1 H'6; try assumption.
    apply H'4 with (y := x0). elim H'3; simpl; auto with sets arith. trivial.
    intros x1 H'4; elim H'4. unfold nat_po; simpl; trivial.
    exists x0.
    apply Upper_Bound_definition.
      unfold nat_po. simpl. apply triv_nat.
    intros y H'1; elim H'1.
    intros x1 H'4; try assumption.
    elim H'3; simpl; auto with sets arith.
    intros x1 H'4; elim H'4; auto with sets arith.
    red.
    intros x1 H'1; elim H'1; apply triv_nat.
  Qed.

  Lemma Integers_has_no_ub :
    ~ (exists m : nat, Upper_Bound nat nat_po Integers m).
  Proof.
    red; intro H'; elim H'.
    intros x H'0.
    elim H'0; intros H'1 H'2.
    cut (In nat Integers (S x)).
    intro H'3.
    specialize H'2 with (y := S x); lapply H'2;
      [ intro H'5; clear H'2 | try assumption; clear H'2 ].
    simpl in H'5.
    absurd (S x <= x); auto with arith.
    apply triv_nat.
 Qed.

  Lemma Integers_infinite : ~ Finite nat Integers.
  Proof.
    generalize Integers_has_no_ub.
    intro H'; red; intro H'0; try exact H'0.
    apply H'.
    apply Finite_subset_has_lub; auto with sets arith.
  Qed.

End Integers_sect.





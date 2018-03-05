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

Section Approx.
  Variable U : Type.

  Inductive Approximant (A X:Ensemble U) : Prop :=
    Defn_of_Approximant : Finite U X -> Included U X A -> Approximant A X.
End Approx.

Hint Resolve Defn_of_Approximant.

Section Infinite_sets.
  Variable U : Type.

  Lemma make_new_approximant :
    forall A X:Ensemble U,
      ~ Finite U A -> Approximant U A X -> Inhabited U (Setminus U A X).
  Proof.
    intros A X H' H'0.
    elim H'0; intros H'1 H'2.
    apply Strict_super_set_contains_new_element; auto with sets.
    red; intro H'3; apply H'.
    rewrite <- H'3; auto with sets.
  Qed.

  Lemma approximants_grow :
    forall A X:Ensemble U,
      ~ Finite U A ->
      forall n:nat,
	cardinal U X n ->
	Included U X A ->  exists Y : _, cardinal U Y (S n) /\ Included U Y A.
  Proof.
    intros A X H' n H'0; elim H'0; auto with sets.
    intro H'1.
    cut (Inhabited U (Setminus U A (Empty_set U))).
    intro H'2; elim H'2.
    intros x H'3.
    exists (Add U (Empty_set U) x); auto with sets.
    split.
    apply card_add; auto with sets.
    cut (In U A x).
    intro H'4; red; auto with sets.
    intros x0 H'5; elim H'5; auto with sets.
    intros x1 H'6; elim H'6; auto with sets.
    elim H'3; auto with sets.
    apply make_new_approximant; auto with sets.
    intros A0 n0 H'1 H'2 x H'3 H'5.
    lapply H'2; [ intro H'6; elim H'6; clear H'2 | clear H'2 ]; auto with sets.
    intros x0 H'2; try assumption.
    elim H'2; intros H'7 H'8; try exact H'8; clear H'2.
    elim (make_new_approximant A x0); auto with sets.
    intros x1 H'2; try assumption.
    exists (Add U x0 x1); auto with sets.
    split.
    apply card_add; auto with sets.
    elim H'2; auto with sets.
    red.
    intros x2 H'9; elim H'9; auto with sets.
    intros x3 H'10; elim H'10; auto with sets.
    elim H'2; auto with sets.
    auto with sets.
    apply Defn_of_Approximant; auto with sets.
    apply cardinal_finite with (n := S n0); auto with sets.
  Qed.

  Lemma approximants_grow' :
    forall A X:Ensemble U,
      ~ Finite U A ->
      forall n:nat,
	cardinal U X n ->
	Approximant U A X ->
	exists Y : _, cardinal U Y (S n) /\ Approximant U A Y.
  Proof.
    intros A X H' n H'0 H'1; try assumption.
    elim H'1.
    intros H'2 H'3.
    elimtype (exists Y : _, cardinal U Y (S n) /\ Included U Y A).
    intros x H'4; elim H'4; intros H'5 H'6; try exact H'5; clear H'4.
    exists x; auto with sets.
    split; [ auto with sets | idtac ].
    apply Defn_of_Approximant; auto with sets.
    apply cardinal_finite with (n := S n); auto with sets.
    apply approximants_grow with (X := X); auto with sets.
  Qed.

  Lemma approximant_can_be_any_size :
    forall A X:Ensemble U,
      ~ Finite U A ->
      forall n:nat,  exists Y : _, cardinal U Y n /\ Approximant U A Y.
  Proof.
    intros A H' H'0 n; elim n.
    exists (Empty_set U); auto with sets.
    intros n0 H'1; elim H'1.
    intros x H'2.
    apply approximants_grow' with (X := x); tauto.
  Qed.

  Variable V : Type.

  Theorem Image_set_continuous :
    forall (A:Ensemble U) (f:U -> V) (X:Ensemble V),
      Finite V X ->
      Included V X (Im U V A f) ->
      exists n : _,
	(exists Y : _, (cardinal U Y n /\ Included U Y A) /\ Im U V Y f = X).
  Proof.
    intros A f X H'; elim H'.
    intro H'0; exists 0.
    exists (Empty_set U); auto with sets.
    intros A0 H'0 H'1 x H'2 H'3; try assumption.
    lapply H'1;
      [ intro H'4; elim H'4; intros n E; elim E; clear H'4 H'1 | clear H'1 ];
      auto with sets.
    intros x0 H'1; try assumption.
    exists (S n); try assumption.
    elim H'1; intros H'4 H'5; elim H'4; intros H'6 H'7; try exact H'6;
      clear H'4 H'1.
    clear E.
    generalize H'2.
    rewrite <- H'5.
    intro H'1; try assumption.
    red in H'3.
    generalize (H'3 x).
    intro H'4; lapply H'4; [ intro H'8; try exact H'8; clear H'4 | clear H'4 ];
      auto with sets.
    specialize Im_inv with (U := U) (V := V) (X := A) (f := f) (y := x);
      intro H'11; lapply H'11; [ intro H'13; elim H'11; clear H'11 | clear H'11 ];
	auto with sets.
    intros x1 H'4; try assumption.
    apply ex_intro with (x := Add U x0 x1).
    split; [ split; [ try assumption | idtac ] | idtac ].
    apply card_add; auto with sets.
    red; intro H'9; try exact H'9.
    apply H'1.
    elim H'4; intros H'10 H'11; rewrite <- H'11; clear H'4; auto with sets.
    elim H'4; intros H'9 H'10; try exact H'9; clear H'4; auto with sets.
    red; auto with sets.
    intros x2 H'4; elim H'4; auto with sets.
    intros x3 H'11; elim H'11; auto with sets.
    elim H'4; intros H'9 H'10; rewrite <- H'10; clear H'4; auto with sets.
    apply Im_add; auto with sets.
  Qed.

  Theorem Image_set_continuous' :
    forall (A:Ensemble U) (f:U -> V) (X:Ensemble V),
      Approximant V (Im U V A f) X ->
      exists Y : _, Approximant U A Y /\ Im U V Y f = X.
  Proof.
    intros A f X H'; try assumption.
    cut
      (exists n : _,
	(exists Y : _, (cardinal U Y n /\ Included U Y A) /\ Im U V Y f = X)).
    intro H'0; elim H'0; intros n E; elim E; clear H'0.
    intros x H'0; try assumption.
    elim H'0; intros H'1 H'2; elim H'1; intros H'3 H'4; try exact H'3;
      clear H'1 H'0; auto with sets.
    exists x.
    split; [ idtac | try assumption ].
    apply Defn_of_Approximant; auto with sets.
    apply cardinal_finite with (n := n); auto with sets.
    apply Image_set_continuous; auto with sets.
    elim H'; auto with sets.
    elim H'; auto with sets.
  Qed.

  Theorem Pigeonhole_bis :
    forall (A:Ensemble U) (f:U -> V),
      ~ Finite U A -> Finite V (Im U V A f) -> ~ injective U V f.
  Proof.
    intros A f H'0 H'1; try assumption.
    elim (Image_set_continuous' A f (Im U V A f)); auto with sets.
    intros x H'2; elim H'2; intros H'3 H'4; try exact H'3; clear H'2.
    elim (make_new_approximant A x); auto with sets.
    intros x0 H'2; elim H'2.
    intros H'5 H'6.
    elim (finite_cardinal V (Im U V A f)); auto with sets.
    intros n E.
    elim (finite_cardinal U x); auto with sets.
    intros n0 E0.
    apply Pigeonhole with (A := Add U x x0) (n := S n0) (n' := n).
    apply card_add; auto with sets.
    rewrite (Im_add U V x x0 f); auto with sets.
    cut (In V (Im U V x f) (f x0)).
    intro H'8.
    rewrite (Non_disjoint_union V (Im U V x f) (f x0)); auto with sets.
    rewrite H'4; auto with sets.
    elim (Extension V (Im U V x f) (Im U V A f)); auto with sets.
    apply le_lt_n_Sm.
    apply cardinal_decreases with (U := U) (V := V) (A := x) (f := f);
      auto with sets.
    rewrite H'4; auto with sets.
    elim H'3; auto with sets.
  Qed.

  Theorem Pigeonhole_ter :
    forall (A:Ensemble U) (f:U -> V) (n:nat),
      injective U V f -> Finite V (Im U V A f) -> Finite U A.
  Proof.
    intros A f H' H'0 H'1.
    apply NNPP.
    red; intro H'2.
    elim (Pigeonhole_bis A f); auto with sets.
  Qed.

End Infinite_sets.

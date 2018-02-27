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

Require Export Ensembles.
Require Export Constructive_sets.
Require Export Relations_1.
Require Export Relations_1_facts.
Require Export Partial_Order.
Require Export Cpo.
Require Export Powerset.
Require Export Powerset_facts.
Require Export Classical.
Require Export Classical_sets.

Section Sets_as_an_algebra.

  Variable U : Type.

  Lemma sincl_add_x :
    forall (A B:Ensemble U) (x:U),
      ~ In U A x ->
      Strict_Included U (Add U A x) (Add U B x) -> Strict_Included U A B.
  Proof.
    intros A B x H' H'0; red.
    lapply (Strict_Included_inv U (Add U A x) (Add U B x)); auto with sets.
    clear H'0; intro H'0; split.
    apply incl_add_x with (x := x); tauto.
    elim H'0; intros H'1 H'2; elim H'2; clear H'0 H'2.
    intros x0 H'0.
    red; intro H'2.
    elim H'0; clear H'0.
    rewrite <- H'2; auto with sets.
  Qed.

  Lemma incl_soustr_in :
    forall (X:Ensemble U) (x:U), In U X x -> Included U (Subtract U X x) X.
  Proof.
    intros X x H'; red.
    intros x0 H'0; elim H'0; auto with sets.
  Qed.

  Lemma incl_soustr :
    forall (X Y:Ensemble U) (x:U),
      Included U X Y -> Included U (Subtract U X x) (Subtract U Y x).
  Proof.
    intros X Y x H'; red.
    intros x0 H'0; elim H'0.
    intros H'1 H'2.
    apply Subtract_intro; auto with sets.
  Qed.

  Lemma incl_soustr_add_l :
    forall (X:Ensemble U) (x:U), Included U (Subtract U (Add U X x) x) X.
  Proof.
    intros X x; red.
    intros x0 H'; elim H'; auto with sets.
    intro H'0; elim H'0; auto with sets.
    intros t H'1 H'2; elim H'2; auto with sets.
  Qed.

  Lemma incl_soustr_add_r :
    forall (X:Ensemble U) (x:U),
      ~ In U X x -> Included U X (Subtract U (Add U X x) x).
  Proof.
    intros X x H'; red.
    intros x0 H'0; try assumption.
    apply Subtract_intro; auto with sets.
    red; intro H'1; apply H'; rewrite H'1; auto with sets.
  Qed.
  Hint Resolve incl_soustr_add_r: sets.

  Lemma add_soustr_2 :
    forall (X:Ensemble U) (x:U),
      In U X x -> Included U X (Add U (Subtract U X x) x).
  Proof.
    intros X x H'; red.
    intros x0 H'0; try assumption.
    elim (classic (x = x0)); intro K; auto with sets.
    elim K; auto with sets.
  Qed.

  Lemma add_soustr_1 :
    forall (X:Ensemble U) (x:U),
      In U X x -> Included U (Add U (Subtract U X x) x) X.
  Proof.
    intros X x H'; red.
    intros x0 H'0; elim H'0; auto with sets.
    intros y H'1; elim H'1; auto with sets.
    intros t H'1; try assumption.
    rewrite <- (Singleton_inv U x t); auto with sets.
  Qed.

  Lemma add_soustr_xy :
    forall (X:Ensemble U) (x y:U),
      x <> y -> Subtract U (Add U X x) y = Add U (Subtract U X y) x.
  Proof.
    intros X x y H'; apply Extensionality_Ensembles.
    split; red.
    intros x0 H'0; elim H'0; auto with sets.
    intro H'1; elim H'1.
    intros u H'2 H'3; try assumption.
    apply Add_intro1.
    apply Subtract_intro; auto with sets.
    intros t H'2 H'3; try assumption.
    elim (Singleton_inv U x t); auto with sets.
    intros u H'2; try assumption.
    elim (Add_inv U (Subtract U X y) x u); auto with sets.
    intro H'0; elim H'0; auto with sets.
    intro H'0; rewrite <- H'0; auto with sets.
  Qed.

  Lemma incl_st_add_soustr :
    forall (X Y:Ensemble U) (x:U),
      ~ In U X x ->
      Strict_Included U (Add U X x) Y -> Strict_Included U X (Subtract U Y x).
  Proof.
    intros X Y x H' H'0; apply sincl_add_x with (x := x); auto using add_soustr_1 with sets.
    split.
    elim H'0.
    intros H'1 H'2.
    generalize (Inclusion_is_transitive U).
    intro H'4; red in H'4.
    apply H'4 with (y := Y); auto using add_soustr_2 with sets.
    red in H'0.
    elim H'0; intros H'1 H'2; try exact H'1; clear H'0. (* PB *)
    red; intro H'0; apply H'2.
    rewrite H'0; auto 8 using add_soustr_xy, add_soustr_1, add_soustr_2 with sets.
  Qed.

  Lemma Sub_Add_new :
    forall (X:Ensemble U) (x:U), ~ In U X x -> X = Subtract U (Add U X x) x.
  Proof.
    auto using incl_soustr_add_l with sets.
  Qed.

  Lemma Simplify_add :
    forall (X X0:Ensemble U) (x:U),
      ~ In U X x -> ~ In U X0 x -> Add U X x = Add U X0 x -> X = X0.
  Proof.
    intros X X0 x H' H'0 H'1; try assumption.
    rewrite (Sub_Add_new X x); auto with sets.
    rewrite (Sub_Add_new X0 x); auto with sets.
    rewrite H'1; auto with sets.
  Qed.

  Lemma Included_Add :
    forall (X A:Ensemble U) (x:U),
      Included U X (Add U A x) ->
      Included U X A \/ (exists A' : _, X = Add U A' x /\ Included U A' A).
  Proof.
    intros X A x H'0; try assumption.
    elim (classic (In U X x)).
    intro H'1; right; try assumption.
    exists (Subtract U X x).
    split; auto using incl_soustr_in, add_soustr_xy, add_soustr_1, add_soustr_2 with sets.
    red in H'0.
    red.
    intros x0 H'2; try assumption.
    lapply (Subtract_inv U X x x0); auto with sets.
    intro H'3; elim H'3; intros K K'; clear H'3.
    lapply (H'0 x0); auto with sets.
    intro H'3; try assumption.
    lapply (Add_inv U A x x0); auto with sets.
    intro H'4; elim H'4;
      [ intro H'5; try exact H'5; clear H'4 | intro H'5; clear H'4 ].
    elim K'; auto with sets.
    intro H'1; left; try assumption.
    red in H'0.
    red.
    intros x0 H'2; try assumption.
    lapply (H'0 x0); auto with sets.
    intro H'3; try assumption.
    lapply (Add_inv U A x x0); auto with sets.
    intro H'4; elim H'4;
      [ intro H'5; try exact H'5; clear H'4 | intro H'5; clear H'4 ].
    absurd (In U X x0); auto with sets.
    rewrite <- H'5; auto with sets.
  Qed.

  Lemma setcover_inv :
    forall A x y:Ensemble U,
      covers (Ensemble U) (Power_set_PO U A) y x ->
      Strict_Included U x y /\
      (forall z:Ensemble U, Included U x z -> Included U z y -> x = z \/ z = y).
  Proof.
    intros A x y H'; elim H'.
    unfold Strict_Rel_of; simpl.
    intros H'0 H'1; split; [ auto with sets | idtac ].
    intros z H'2 H'3; try assumption.
    elim (classic (x = z)); auto with sets.
    intro H'4; right; try assumption.
    elim (classic (z = y)); auto with sets.
    intro H'5; try assumption.
    elim H'1.
    exists z; auto with sets.
  Qed.

  Theorem Add_covers :
    forall A a:Ensemble U,
      Included U a A ->
      forall x:U,
	In U A x ->
	~ In U a x -> covers (Ensemble U) (Power_set_PO U A) (Add U a x) a.
  Proof.
    intros A a H' x H'0 H'1; try assumption.
    apply setcover_intro; auto with sets.
    red.
    split; [ idtac | red; intro H'2; try exact H'2 ]; auto with sets.
    apply H'1.
    rewrite H'2; auto with sets.
    red; intro H'2; elim H'2; clear H'2.
    intros z H'2; elim H'2; intros H'3 H'4; try exact H'3; clear H'2.
    lapply (Strict_Included_inv U a z); auto with sets; clear H'3.
    intro H'2; elim H'2; intros H'3 H'5; elim H'5; clear H'2 H'5.
    intros x0 H'2; elim H'2.
    intros H'5 H'6; try assumption.
    generalize H'4; intro K.
    red in H'4.
    elim H'4; intros H'8 H'9; red in H'8; clear H'4.
    lapply (H'8 x0); auto with sets.
    intro H'7; try assumption.
    elim (Add_inv U a x x0); auto with sets.
    intro H'15.
    cut (Included U (Add U a x) z).
    intro H'10; try assumption.
    red in K.
    elim K; intros H'11 H'12; apply H'12; clear K; auto with sets.
    rewrite H'15.
    red.
    intros x1 H'10; elim H'10; auto with sets.
    intros x2 H'11; elim H'11; auto with sets.
  Qed.

  Theorem covers_Add :
    forall A a a':Ensemble U,
      Included U a A ->
      Included U a' A ->
      covers (Ensemble U) (Power_set_PO U A) a' a ->
      exists x : _, a' = Add U a x /\ In U A x /\ ~ In U a x.
  Proof.
    intros A a a' H' H'0 H'1; try assumption.
    elim (setcover_inv A a a'); auto with sets.
    intros H'6 H'7.
    clear H'1.
    elim (Strict_Included_inv U a a'); auto with sets.
    intros H'5 H'8; elim H'8.
    intros x H'1; elim H'1.
    intros H'2 H'3; try assumption.
    exists x.
    split; [ try assumption | idtac ].
    clear H'8 H'1.
    elim (H'7 (Add U a x)); auto with sets.
    intro H'1.
    absurd (a = Add U a x); auto with sets.
    red; intro H'8; try exact H'8.
    apply H'3.
    rewrite H'8; auto with sets.
    auto with sets.
    red.
    intros x0 H'1; elim H'1; auto with sets.
    intros x1 H'8; elim H'8; auto with sets.
    split; [ idtac | try assumption ].
    red in H'0; auto with sets.
  Qed.

  Theorem covers_is_Add :
    forall A a a':Ensemble U,
      Included U a A ->
      Included U a' A ->
      (covers (Ensemble U) (Power_set_PO U A) a' a <->
	(exists x : _, a' = Add U a x /\ In U A x /\ ~ In U a x)).
  Proof.
    intros A a a' H' H'0; split; intro K.
    apply covers_Add with (A := A); auto with sets.
    elim K.
    intros x H'1; elim H'1; intros H'2 H'3; rewrite H'2; clear H'1.
    apply Add_covers; intuition.
  Qed.

  Theorem Singleton_atomic :
    forall (x:U) (A:Ensemble U),
      In U A x ->
      covers (Ensemble U) (Power_set_PO U A) (Singleton U x) (Empty_set U).
  Proof.
    intros x A H'.
    rewrite <- (Empty_set_zero' U x).
    apply Add_covers; auto with sets.
  Qed.

  Lemma less_than_singleton :
    forall (X:Ensemble U) (x:U),
      Strict_Included U X (Singleton U x) -> X = Empty_set U.
  Proof.
    intros X x H'; try assumption.
    red in H'.
    lapply (Singleton_atomic x (Full_set U));
      [ intro H'2; try exact H'2 | apply Full_intro ].
    elim H'; intros H'0 H'1; try exact H'1; clear H'.
    elim (setcover_inv (Full_set U) (Empty_set U) (Singleton U x));
      [ intros H'6 H'7; try exact H'7 | idtac ]; auto with sets.
    elim (H'7 X); [ intro H'5; try exact H'5 | intro H'5 | idtac | idtac ];
      auto with sets.
    elim H'1; auto with sets.
  Qed.

End Sets_as_an_algebra.

Hint Resolve incl_soustr_in: sets.
Hint Resolve incl_soustr: sets.
Hint Resolve incl_soustr_add_l: sets.
Hint Resolve incl_soustr_add_r: sets.
Hint Resolve add_soustr_1 add_soustr_2: sets.
Hint Resolve add_soustr_xy: sets.

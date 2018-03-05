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
Require Export Classical.

Section Ensembles_classical.
  Variable U : Type.

  Lemma not_included_empty_Inhabited :
    forall A:Ensemble U, ~ Included U A (Empty_set U) -> Inhabited U A.
  Proof.
    intros A NI.
    elim (not_all_ex_not U (fun x:U => ~ In U A x)).
    intros x H; apply Inhabited_intro with x.
    apply NNPP; auto with sets.
    red; intro.
    apply NI; red.
    intros x H'; elim (H x); trivial with sets.
  Qed.

  Lemma not_empty_Inhabited :
    forall A:Ensemble U, A <> Empty_set U -> Inhabited U A.
  Proof.
    intros; apply not_included_empty_Inhabited.
    red; auto with sets.
  Qed.

  Lemma Inhabited_Setminus :
    forall X Y:Ensemble U,
      Included U X Y -> ~ Included U Y X -> Inhabited U (Setminus U Y X).
  Proof.
    intros X Y I NI.
    elim (not_all_ex_not U (fun x:U => In U Y x -> In U X x) NI).
    intros x YX.
    apply Inhabited_intro with x.
    apply Setminus_intro.
    apply not_imply_elim with (In U X x); trivial with sets.
    auto with sets.
  Qed.

  Lemma Strict_super_set_contains_new_element :
    forall X Y:Ensemble U,
      Included U X Y -> X <> Y -> Inhabited U (Setminus U Y X).
  Proof.
    auto 7 using Inhabited_Setminus with sets.
  Qed.

  Lemma Subtract_intro :
    forall (A:Ensemble U) (x y:U), In U A y -> x <> y -> In U (Subtract U A x) y.
  Proof.
    unfold Subtract at 1; auto with sets.
  Qed.
  Hint Resolve Subtract_intro : sets.

  Lemma Subtract_inv :
    forall (A:Ensemble U) (x y:U), In U (Subtract U A x) y -> In U A y /\ x <> y.
  Proof.
    intros A x y H'; elim H'; auto with sets.
  Qed.

  Lemma Included_Strict_Included :
    forall X Y:Ensemble U, Included U X Y -> Strict_Included U X Y \/ X = Y.
  Proof.
    intros X Y H'; try assumption.
    elim (classic (X = Y)); auto with sets.
  Qed.

  Lemma Strict_Included_inv :
    forall X Y:Ensemble U,
      Strict_Included U X Y -> Included U X Y /\ Inhabited U (Setminus U Y X).
  Proof.
    intros X Y H'; red in H'.
    split; [ tauto | idtac ].
    elim H'; intros H'0 H'1; try exact H'1; clear H'.
    apply Strict_super_set_contains_new_element; auto with sets.
  Qed.

  Lemma not_SIncl_empty :
    forall X:Ensemble U, ~ Strict_Included U X (Empty_set U).
  Proof.
    intro X; red; intro H'; try exact H'.
    lapply (Strict_Included_inv X (Empty_set U)); auto with sets.
    intro H'0; elim H'0; intros H'1 H'2; elim H'2; clear H'0.
    intros x H'0; elim H'0.
    intro H'3; elim H'3.
  Qed.

  Lemma Complement_Complement :
    forall A:Ensemble U, Complement U (Complement U A) = A.
  Proof.
    unfold Complement; intros; apply Extensionality_Ensembles;
      auto with sets.
    red; split; auto with sets.
    red; intros; apply NNPP; auto with sets.
  Qed.

End Ensembles_classical.

 Hint Resolve Strict_super_set_contains_new_element Subtract_intro
  not_SIncl_empty: sets.

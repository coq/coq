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

Section Image.
  Variables U V : Type.

  Inductive Im (X:Ensemble U) (f:U -> V) : Ensemble V :=
    Im_intro : forall x:U, In _ X x -> forall y:V, y = f x -> In _ (Im X f) y.

  Lemma Im_def :
    forall (X:Ensemble U) (f:U -> V) (x:U), In _ X x -> In _ (Im X f) (f x).
  Proof.
    intros X f x H'; try assumption.
    apply Im_intro with (x := x); auto with sets.
  Qed.

  Lemma Im_add :
    forall (X:Ensemble U) (x:U) (f:U -> V),
      Im (Add _ X x) f = Add _ (Im X f) (f x).
  Proof.
    intros X x f.
    apply Extensionality_Ensembles.
    split; red; intros x0 H'.
    elim H'; intros.
    rewrite H0.
    elim Add_inv with U X x x1; auto using Im_def with sets.
    destruct 1; auto using Im_def with sets.
    elim Add_inv with V (Im X f) (f x) x0.
    destruct 1 as [x0 H y H0].
    rewrite H0; auto using Im_def with sets.
    destruct 1; auto using Im_def with sets.
    trivial.
  Qed.

  Lemma image_empty : forall f:U -> V, Im (Empty_set U) f = Empty_set V.
  Proof.
    intro f; try assumption.
    apply Extensionality_Ensembles.
    split; auto with sets.
    red.
    intros x H'; elim H'.
    intros x0 H'0; elim H'0; auto with sets.
  Qed.

  Lemma finite_image :
    forall (X:Ensemble U) (f:U -> V), Finite _ X -> Finite _ (Im X f).
  Proof.
    intros X f H'; elim H'.
    rewrite (image_empty f); auto with sets.
    intros A H'0 H'1 x H'2; clear H' X.
    rewrite (Im_add A x f); auto with sets.
    apply Add_preserves_Finite; auto with sets.
  Qed.

  Lemma Im_inv :
    forall (X:Ensemble U) (f:U -> V) (y:V),
      In _ (Im X f) y ->  exists x : U, In _ X x /\ f x = y.
  Proof.
    intros X f y H'; elim H'.
    intros x H'0 y0 H'1; rewrite H'1.
    exists x; auto with sets.
  Qed.

  Definition injective (f:U -> V) := forall x y:U, f x = f y -> x = y.

  Lemma not_injective_elim :
    forall f:U -> V,
      ~ injective f ->  exists x : _, (exists y : _, f x = f y /\ x <> y).
  Proof.
    unfold injective; intros f H.
    cut (exists x : _, ~ (forall y:U, f x = f y -> x = y)).
    2: apply not_all_ex_not with (P := fun x:U => forall y:U, f x = f y -> x = y);
      trivial with sets.
    destruct 1 as [x C]; exists x.
    cut (exists y : _, ~ (f x = f y -> x = y)).
    2: apply not_all_ex_not with (P := fun y:U => f x = f y -> x = y);
      trivial with sets.
    destruct 1 as [y D]; exists y.
    apply imply_to_and; trivial with sets.
  Qed.

  Lemma cardinal_Im_intro :
    forall (A:Ensemble U) (f:U -> V) (n:nat),
      cardinal _ A n ->  exists p : nat, cardinal _ (Im A f) p.
  Proof.
    intros.
    apply finite_cardinal; apply finite_image.
    apply cardinal_finite with n; trivial with sets.
  Qed.

  Lemma In_Image_elim :
    forall (A:Ensemble U) (f:U -> V),
      injective f -> forall x:U, In _ (Im A f) (f x) -> In _ A x.
  Proof.
    intros.
    elim Im_inv with A f (f x); trivial with sets.
    intros z C; elim C; intros InAz E.
    elim (H z x E); trivial with sets.
  Qed.

  Lemma injective_preserves_cardinal :
    forall (A:Ensemble U) (f:U -> V) (n:nat),
      injective f ->
      cardinal _ A n -> forall n':nat, cardinal _ (Im A f) n' -> n' = n.
  Proof.
    induction 2 as [| A n H'0 H'1 x H'2]; auto with sets.
    rewrite (image_empty f).
    intros n' CE.
    apply cardinal_unicity with V (Empty_set V); auto with sets.
    intro n'.
    rewrite (Im_add A x f).
    intro H'3.
    elim cardinal_Im_intro with A f n; trivial with sets.
    intros i CI.
    lapply (H'1 i); trivial with sets.
    cut (~ In _ (Im A f) (f x)).
    intros H0 H1.
    apply cardinal_unicity with V (Add _ (Im A f) (f x)); trivial with sets.
    apply card_add; auto with sets.
    rewrite <- H1; trivial with sets.
    red; intro; apply H'2.
    apply In_Image_elim with f; trivial with sets.
  Qed.

  Lemma cardinal_decreases :
    forall (A:Ensemble U) (f:U -> V) (n:nat),
      cardinal U A n -> forall n':nat, cardinal V (Im A f) n' -> n' <= n.
  Proof.
    induction 1 as [| A n H'0 H'1 x H'2]; auto with sets.
    rewrite (image_empty f); intros.
    cut (n' = 0).
    intro E; rewrite E; trivial with sets.
    apply cardinal_unicity with V (Empty_set V); auto with sets.
    intro n'.
    rewrite (Im_add A x f).
    elim cardinal_Im_intro with A f n; trivial with sets.
    intros p C H'3.
    apply le_trans with (S p).
    apply card_Add_gen with V (Im A f) (f x); trivial with sets.
    apply le_n_S; auto with sets.
  Qed.

  Theorem Pigeonhole :
    forall (A:Ensemble U) (f:U -> V) (n:nat),
      cardinal U A n ->
      forall n':nat, cardinal V (Im A f) n' -> n' < n -> ~ injective f.
  Proof.
    unfold not; intros A f n CAn n' CIfn' ltn'n I.
    cut (n' = n).
    intro E; generalize ltn'n; rewrite E; exact (lt_irrefl n).
    apply injective_preserves_cardinal with (A := A) (f := f) (n := n);
      trivial with sets.
  Qed.

  Lemma Pigeonhole_principle :
    forall (A:Ensemble U) (f:U -> V) (n:nat),
      cardinal _ A n ->
      forall n':nat,
	cardinal _ (Im A f) n' ->
	n' < n ->  exists x : _, (exists y : _, f x = f y /\ x <> y).
  Proof.
    intros; apply not_injective_elim.
    apply Pigeonhole with A n n'; trivial with sets.
  Qed.

End Image.

Hint Resolve Im_def image_empty finite_image: sets.

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

Section Finite_sets_facts.
  Variable U : Type.

  Lemma finite_cardinal :
    forall X:Ensemble U, Finite U X ->  exists n : nat, cardinal U X n.
  Proof.
    induction 1 as [| A _ [n H]].
    exists 0; auto with sets.
    exists (S n); auto with sets.
  Qed.

  Lemma cardinal_finite :
    forall (X:Ensemble U) (n:nat), cardinal U X n -> Finite U X.
  Proof.
    induction 1; auto with sets.
  Qed.

  Theorem Add_preserves_Finite :
    forall (X:Ensemble U) (x:U), Finite U X -> Finite U (Add U X x).
  Proof.
    intros X x H'.
    elim (classic (In U X x)); intro H'0; auto with sets.
    rewrite (Non_disjoint_union U X x); auto with sets.
  Qed.

  Theorem Singleton_is_finite : forall x:U, Finite U (Singleton U x).
  Proof.
    intro x; rewrite <- (Empty_set_zero U (Singleton U x)).
    change (Finite U (Add U (Empty_set U) x)); auto with sets.
  Qed.

  Theorem Union_preserves_Finite :
    forall X Y:Ensemble U, Finite U X -> Finite U Y -> Finite U (Union U X Y).
  Proof.
    intros X Y H; induction H as [|A Fin_A Hind x].
    rewrite (Empty_set_zero U Y). trivial.
    intros.
    rewrite (Union_commutative U (Add U A x) Y).
    rewrite <- (Union_add U Y A x).
    rewrite (Union_commutative U Y A).
    apply Add_preserves_Finite.
    apply Hind. assumption.
  Qed.

  Lemma Finite_downward_closed :
    forall A:Ensemble U,
      Finite U A -> forall X:Ensemble U, Included U X A -> Finite U X.
  Proof.
    intros A H'; elim H'; auto with sets.
    intros X H'0.
    rewrite (less_than_empty U X H'0); auto with sets.
    intros; elim Included_Add with U X A0 x; auto with sets.
    destruct 1 as [A' [H5 H6]].
    rewrite H5; auto with sets.
  Qed.

  Lemma Intersection_preserves_finite :
    forall A:Ensemble U,
      Finite U A -> forall X:Ensemble U, Finite U (Intersection U X A).
  Proof.
    intros A H' X; apply Finite_downward_closed with A; auto with sets.
  Qed.

  Lemma cardinalO_empty :
    forall X:Ensemble U, cardinal U X 0 -> X = Empty_set U.
  Proof.
    intros X H; apply (cardinal_invert U X 0); trivial with sets.
  Qed.

  Lemma inh_card_gt_O :
    forall X:Ensemble U, Inhabited U X -> forall n:nat, cardinal U X n -> n > 0.
  Proof.
    induction 1 as [x H'].
    intros n H'0.
    elim (gt_O_eq n); auto with sets.
    intro H'1; generalize H'; generalize H'0.
    rewrite <- H'1; intro H'2.
    rewrite (cardinalO_empty X); auto with sets.
    intro H'3; elim H'3.
  Qed.

  Lemma card_soustr_1 :
    forall (X:Ensemble U) (n:nat),
      cardinal U X n ->
      forall x:U, In U X x -> cardinal U (Subtract U X x) (pred n).
  Proof.
    intros X n H'; elim H'.
    intros x H'0; elim H'0.
    clear H' n X.
    intros X n H' H'0 x H'1 x0 H'2.
    elim (classic (In U X x0)).
    intro H'4; rewrite (add_soustr_xy U X x x0).
    elim (classic (x = x0)).
    intro H'5.
    absurd (In U X x0); auto with sets.
    rewrite <- H'5; auto with sets.
    intro H'3; try assumption.
    cut (S (pred n) = pred (S n)).
    intro H'5; rewrite <- H'5.
    apply card_add; auto with sets.
    red; intro H'6; elim H'6.
    intros H'7 H'8; try assumption.
    elim H'1; auto with sets.
    unfold pred at 2; symmetry .
    apply S_pred with (m := 0).
    change (n > 0).
    apply inh_card_gt_O with (X := X); auto with sets.
    apply Inhabited_intro with (x := x0); auto with sets.
    red; intro H'3.
    apply H'1.
    elim H'3; auto with sets.
    rewrite H'3; auto with sets.
    elim (classic (x = x0)).
    intro H'3; rewrite <- H'3.
    cut (Subtract U (Add U X x) x = X); auto with sets.
    intro H'4; rewrite H'4; auto with sets.
    intros H'3 H'4; try assumption.
    absurd (In U (Add U X x) x0); auto with sets.
    red; intro H'5; try exact H'5.
    lapply (Add_inv U X x x0); tauto.
  Qed.

  Lemma cardinal_is_functional :
    forall (X:Ensemble U) (c1:nat),
      cardinal U X c1 ->
      forall (Y:Ensemble U) (c2:nat), cardinal U Y c2 -> X = Y -> c1 = c2.
  Proof.
    intros X c1 H'; elim H'.
    intros Y c2 H'0; elim H'0; auto with sets.
    intros A n H'1 H'2 x H'3 H'5.
    elim (not_Empty_Add U A x); auto with sets.
    clear H' c1 X.
    intros X n H' H'0 x H'1 Y c2 H'2.
    elim H'2.
    intro H'3.
    elim (not_Empty_Add U X x); auto with sets.
    clear H'2 c2 Y.
    intros X0 c2 H'2 H'3 x0 H'4 H'5.
    elim (classic (In U X0 x)).
    intro H'6; apply f_equal.
    apply H'0 with (Y := Subtract U (Add U X0 x0) x).
    elimtype (pred (S c2) = c2); auto with sets.
    apply card_soustr_1; auto with sets.
    rewrite <- H'5.
    apply Sub_Add_new; auto with sets.
    elim (classic (x = x0)).
    intros H'6 H'7; apply f_equal.
    apply H'0 with (Y := X0); auto with sets.
    apply Simplify_add with (x := x); auto with sets.
    pattern x at 2; rewrite H'6; auto with sets.
    intros H'6 H'7.
    absurd (Add U X x = Add U X0 x0); auto with sets.
    clear H'0 H' H'3 n H'5 H'4 H'2 H'1 c2.
    red; intro H'.
    lapply (Extension U (Add U X x) (Add U X0 x0)); auto with sets.
    clear H'.
    intro H'; red in H'.
    elim H'; intros H'0 H'1; red in H'0; clear H' H'1.
    absurd (In U (Add U X0 x0) x); auto with sets.
    lapply (Add_inv U X0 x0 x); [ intuition | apply (H'0 x); apply Add_intro2 ].
  Qed.

  Lemma cardinal_Empty : forall m:nat, cardinal U (Empty_set U) m -> 0 = m.
  Proof.
    intros m Cm; generalize (cardinal_invert U (Empty_set U) m Cm).
    elim m; auto with sets.
    intros; elim H0; intros; elim H1; intros; elim H2; intros.
    elim (not_Empty_Add U x x0 H3).
  Qed.

  Lemma cardinal_unicity :
    forall (X:Ensemble U) (n:nat),
      cardinal U X n -> forall m:nat, cardinal U X m -> n = m.
  Proof.
    intros; apply cardinal_is_functional with X X; auto with sets.
  Qed.

  Lemma card_Add_gen :
    forall (A:Ensemble U) (x:U) (n n':nat),
      cardinal U A n -> cardinal U (Add U A x) n' -> n' <= S n.
  Proof.
    intros A x n n' H'.
    elim (classic (In U A x)).
    intro H'0.
    rewrite (Non_disjoint_union U A x H'0).
    intro H'1; cut (n = n').
    intro E; rewrite E; auto with sets.
    apply cardinal_unicity with A; auto with sets.
    intros H'0 H'1.
    cut (n' = S n).
    intro E; rewrite E; auto with sets.
    apply cardinal_unicity with (Add U A x); auto with sets.
  Qed.

  Lemma incl_st_card_lt :
    forall (X:Ensemble U) (c1:nat),
      cardinal U X c1 ->
      forall (Y:Ensemble U) (c2:nat),
	cardinal U Y c2 -> Strict_Included U X Y -> c2 > c1.
  Proof.
    intros X c1 H'; elim H'.
    intros Y c2 H'0; elim H'0; auto with sets arith.
    intro H'1.
    elim (Strict_Included_strict U (Empty_set U)); auto with sets arith.
    clear H' c1 X.
    intros X n H' H'0 x H'1 Y c2 H'2.
    elim H'2.
    intro H'3; elim (not_SIncl_empty U (Add U X x)); auto with sets arith.
    clear H'2 c2 Y.
    intros X0 c2 H'2 H'3 x0 H'4 H'5; elim (classic (In U X0 x)).
    intro H'6; apply gt_n_S.
    apply H'0 with (Y := Subtract U (Add U X0 x0) x).
    elimtype (pred (S c2) = c2); auto with sets arith.
    apply card_soustr_1; auto with sets arith.
    apply incl_st_add_soustr; auto with sets arith.
    elim (classic (x = x0)).
    intros H'6 H'7; apply gt_n_S.
    apply H'0 with (Y := X0); auto with sets arith.
    apply sincl_add_x with (x := x0).
    rewrite <- H'6; auto with sets arith.
    pattern x0 at 1; rewrite <- H'6; trivial with sets arith.
    intros H'6 H'7; red in H'5.
    elim H'5; intros H'8 H'9; try exact H'8; clear H'5.
    red in H'8.
    generalize (H'8 x).
    intro H'5; lapply H'5; auto with sets arith.
    intro H; elim Add_inv with U X0 x0 x; auto with sets arith.
    intro; absurd (In U X0 x); auto with sets arith.
    intro; absurd (x = x0); auto with sets arith.
  Qed.

  Lemma incl_card_le :
    forall (X Y:Ensemble U) (n m:nat),
      cardinal U X n -> cardinal U Y m -> Included U X Y -> n <= m.
  Proof.
    intros; elim Included_Strict_Included with U X Y; auto with sets arith; intro.
    cut (m > n); auto with sets arith.
    apply incl_st_card_lt with (X := X) (Y := Y); auto with sets arith.
    generalize H0; rewrite <- H2; intro.
    cut (n = m).
    intro E; rewrite E; auto with sets arith.
    apply cardinal_unicity with X; auto with sets arith.
  Qed.

  Lemma G_aux :
    forall P:Ensemble U -> Prop,
      (forall X:Ensemble U,
	Finite U X ->
	(forall Y:Ensemble U, Strict_Included U Y X -> P Y) -> P X) ->
      P (Empty_set U).
  Proof.
    intros P H'; try assumption.
    apply H'; auto with sets.
    clear H'; auto with sets.
    intros Y H'; try assumption.
    red in H'.
    elim H'; intros H'0 H'1; try exact H'1; clear H'.
    lapply (less_than_empty U Y); [ intro H'3; try exact H'3 | assumption ].
    elim H'1; auto with sets.
  Qed.

  Lemma Generalized_induction_on_finite_sets :
    forall P:Ensemble U -> Prop,
      (forall X:Ensemble U,
	Finite U X ->
	(forall Y:Ensemble U, Strict_Included U Y X -> P Y) -> P X) ->
      forall X:Ensemble U, Finite U X -> P X.
  Proof.
    intros P H'0 X H'1.
    generalize P H'0; clear H'0 P.
    elim H'1.
    intros P H'0.
    apply G_aux; auto with sets.
    clear H'1 X.
    intros A H' H'0 x H'1 P H'3.
    cut (forall Y:Ensemble U, Included U Y (Add U A x) -> P Y); auto with sets.
    generalize H'1.
    apply H'0.
    intros X K H'5 L Y H'6; apply H'3; auto with sets.
    apply Finite_downward_closed with (A := Add U X x); auto with sets.
    intros Y0 H'7.
    elim (Strict_inclusion_is_transitive_with_inclusion U Y0 Y (Add U X x));
      auto with sets.
    intros H'2 H'4.
    elim (Included_Add U Y0 X x);
      [ intro H'14
	| intro H'14; elim H'14; intros A' E; elim E; intros H'15 H'16; clear E H'14
	| idtac ]; auto with sets.
    elim (Included_Strict_Included U Y0 X); auto with sets.
    intro H'9; apply H'5 with (Y := Y0); auto with sets.
    intro H'9; rewrite H'9.
    apply H'3; auto with sets.
    intros Y1 H'8; elim H'8.
    intros H'10 H'11; apply H'5 with (Y := Y1); auto with sets.
    elim (Included_Strict_Included U A' X); auto with sets.
    intro H'8; apply H'5 with (Y := A'); auto with sets.
    rewrite <- H'15; auto with sets.
    intro H'8.
    elim H'7.
    intros H'9 H'10; apply H'10 || elim H'10; try assumption.
    generalize H'6.
    rewrite <- H'8.
    rewrite <- H'15; auto with sets.
  Qed.

End Finite_sets_facts.

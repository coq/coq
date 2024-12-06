(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
Require Export PeanoNat.

Section Finite_sets_facts.
  Variable U : Type.

  Lemma finite_cardinal :
    forall X:Ensemble U, Finite U X ->  exists n : nat, cardinal U X n.
  Proof.
    induction 1 as [| A _ [n H]].
    - exists 0; auto with sets.
    - exists (S n); auto with sets.
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
    intro x; rewrite <- Empty_set_zero'.
    apply Union_is_finite; auto with sets.
  Qed.

  Theorem Union_preserves_Finite :
    forall X Y:Ensemble U, Finite U X -> Finite U Y -> Finite U (Union U X Y).
  Proof.
    intros X Y HX HY.
    induction HX.
    - now rewrite Empty_set_zero.
    - rewrite Union_commutative.
      rewrite <- Union_add.
      apply Add_preserves_Finite.
      now rewrite Union_commutative.
  Qed.

  Lemma Finite_downward_closed :
    forall A:Ensemble U,
      Finite U A -> forall X:Ensemble U, Included U X A -> Finite U X.
  Proof.
    intros A HA.
    induction HA as [|A HA IHHA]; [ intros X HX | intros X HXAx ].
    - rewrite less_than_empty; auto with sets.
    - destruct (Included_Add _ _ _ _ HXAx) as [|[X' [-> HX'A]]]; auto with sets.
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
    intros X [x HX] [] HCX.
    - now rewrite (cardinalO_empty X HCX) in HX.
    - apply Nat.lt_0_succ.
  Qed.

  Lemma card_soustr_1 :
    forall (X:Ensemble U) (n:nat),
      cardinal U X n ->
      forall x:U, In U X x -> cardinal U (Subtract U X x) (pred n).
  Proof.
    intros X n H. induction H as [|X n H IH x Hx]; intros x' Hx'.
    - destruct Hx'.
    - rewrite Nat.pred_succ.
      apply Add_inv in Hx' as [Hx' | <-].
      + rewrite (add_soustr_xy _ _ x x') by (intros <-; contradiction Hx).
        rewrite <- Nat.succ_pred_pos.
        * apply card_add; [ apply (IH _ Hx') |].
          now intros [? _]%Subtract_inv.
        * apply inh_card_gt_O with (X := X); [| assumption ].
          exact (Inhabited_intro _ _ _ Hx').
      + rewrite <- (Sub_Add_new _ _ _ Hx). assumption.
  Qed.

  Lemma cardinal_Empty : forall m:nat, cardinal U (Empty_set U) m -> 0 = m.
  Proof.
    intros m Cm.
    inversion Cm as [|X n _ x _ H]; [ reflexivity | ].
    symmetry in H.
    now apply not_Empty_Add in H.
  Qed.

  Lemma cardinal_is_functional :
    forall (X:Ensemble U) (c1:nat),
      cardinal U X c1 ->
      forall (Y:Ensemble U) (c2:nat), cardinal U Y c2 -> X = Y -> c1 = c2.
  Proof.
    intros X c1 H'; elim H'.
    - intros Y c2 H'0 <-; now apply cardinal_Empty.
    - clear H' c1 X.
      intros X n H' H'0 x H'1 Y c2 H'2.
      elim H'2.
      + intro H'3; now elim (not_Empty_Add U X x).
      + clear H'2 c2 Y.
        intros X0 c2 H'2 _ x0 H'4 H'5.
        apply f_equal.
        assert (H'6 : In U (Add U X x) x) by apply Add_intro2.
        rewrite H'5 in H'6.
        destruct (Add_inv _ _ _ _ H'6) as [H'7 | <-].
        * apply H'0 with (Y := Subtract U (Add U X0 x0) x).
          -- rewrite <- Nat.pred_succ; apply card_soustr_1; auto with sets.
          -- rewrite <- H'5; auto with sets.
        * apply (H'0 _ _ H'2 (Simplify_add _ _ _ _ H'1 H'4 H'5)).
  Qed.

  Lemma cardinal_unicity :
    forall (X:Ensemble U) (n:nat),
      cardinal U X n -> forall m:nat, cardinal U X m -> n = m.
  Proof.
    intros X ? ? ? ?; now apply cardinal_is_functional with X X.
  Qed.

  Lemma card_Add_gen :
    forall (A:Ensemble U) (x:U) (n n':nat),
      cardinal U A n -> cardinal U (Add U A x) n' -> n' <= S n.
  Proof.
    intros A x n n' H0 H1.
    elim (classic (In U A x)); intro H2.
    - rewrite (Non_disjoint_union _ _ _ H2) in H1.
      rewrite (cardinal_unicity _ _ H0 _ H1).
      apply Nat.le_succ_diag_r.
    - apply Nat.eq_le_incl.
      apply cardinal_unicity with (X := Add U A x); auto with sets.
  Qed.

  Lemma incl_st_card_lt :
    forall (X:Ensemble U) (c1:nat),
      cardinal U X c1 ->
      forall (Y:Ensemble U) (c2:nat),
        cardinal U Y c2 -> Strict_Included U X Y -> c2 > c1.
  Proof.
    intros X c1 H1.
    induction H1 as [|X' ? HX' IH x Hx]; intros Y c2 HY Hsincl;
      (inversion HY as [HXY Hc | ? ? ? ? ? HXY]; subst Y; [ apply not_SIncl_empty in Hsincl as [] |]).
    - apply Nat.lt_0_succ.
    - subst c2. apply -> Nat.succ_lt_mono.
      refine (IH _ _ _ (incl_st_add_soustr _ _ _ _ Hx Hsincl)).
      rewrite <- Nat.pred_succ. apply card_soustr_1; [ assumption | ].
      apply Hsincl, Add_intro2.
  Qed.

  Lemma incl_card_le :
    forall (X Y:Ensemble U) (n m:nat),
      cardinal U X n -> cardinal U Y m -> Included U X Y -> n <= m.
  Proof.
    intros X Y n m HX HY HXY.
    destruct (Included_Strict_Included _ _ _ HXY) as [HXY' | <-].
    - apply Nat.lt_le_incl.
      now apply (incl_st_card_lt _ _ HX _ _ HY).
    - apply Nat.eq_le_incl.
      now apply cardinal_unicity with X.
  Qed.

  Lemma Generalized_induction_on_finite_sets :
    forall P:Ensemble U -> Prop,
      (forall X:Ensemble U,
        Finite U X ->
        (forall Y:Ensemble U, Strict_Included U Y X -> P Y) -> P X) ->
      forall X:Ensemble U, Finite U X -> P X.
  Proof.
    intros P HP X HX.
    induction HX as [|X HX IH x Hx] in P, HP.
    - apply HP; [ auto with sets | ].
      now intros Y [->%less_than_empty []].
    - enough (forall Y, Included U Y (Add U X x) -> P Y) by auto with sets.
      revert Hx. apply IH. clear IH X HX.
      intros Y HY IH' Hx Z HZYx.
      apply HP; [ apply Finite_downward_closed with (Add _ Y x); auto with sets | ].
      intros Z' HZ'Z.
      pose proof (Strict_inclusion_is_transitive_with_inclusion _ _ _ _ HZ'Z HZYx) as [HZ'Yx Hneq].
      case (Included_Add _ _ _ _ HZ'Yx) as [HZ'Y | [Y' [-> HY'Y]]].
      + case (classic (Z' = Y)) as [-> | Hneq'].
        * apply (HP _ HY).
          intros Y' [HY'Y Hneq'].
          apply (IH' Y'); auto with sets.
        * apply (IH' Z'); auto with sets.
      + apply (IH' Y'); auto with sets.
        now split; [| intros -> ].
  Qed.

End Finite_sets_facts.

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

Section Finite_sets_facts.
Variable U: Type.

Lemma finite_cardinal :
 (X: (Ensemble U)) (Finite U X) -> (EX n:nat |(cardinal U X n)).
Proof.
NewInduction 1 as [|A _ [n H]].
Exists O; Auto with sets.
Exists (S n); Auto with sets.
Qed.

Lemma cardinal_finite:
  (X: (Ensemble U)) (n: nat) (cardinal U X n) -> (Finite U X).
Proof.
NewInduction 1; Auto with sets.
Qed.

Theorem Add_preserves_Finite:
  (X: (Ensemble U)) (x: U) (Finite U X) -> (Finite U (Add U X x)).
Proof.
Intros X x H'.
Elim (classic (In U X x)); Intro H'0; Auto with sets.
Rewrite (Non_disjoint_union U X x); Auto with sets.
Qed.
Hints Resolve Add_preserves_Finite.

Theorem Singleton_is_finite: (x: U) (Finite U (Singleton U x)).
Proof.
Intro x; Rewrite <- (Empty_set_zero U (Singleton U x)).
Change (Finite U (Add U (Empty_set U) x)); Auto with sets.
Qed.
Hints Resolve Singleton_is_finite.

Theorem Union_preserves_Finite:
  (X, Y: (Ensemble U)) (Finite U X) -> (Finite U Y) -> 
                       (Finite U (Union U X Y)).
Proof.
Intros X Y H'; Elim H'.
Rewrite (Empty_set_zero U Y); Auto with sets.
Intros A H'0 H'1 x H'2 H'3.
Rewrite (Union_commutative U (Add U A x) Y).
Rewrite <- (Union_add U Y A x).
Rewrite (Union_commutative U Y A); Auto with sets.
Qed.

Lemma Finite_downward_closed:
  (A: (Ensemble U)) (Finite U A) ->
   (X: (Ensemble U)) (Included U X A) -> (Finite U X).
Proof.
Intros A H'; Elim H'; Auto with sets.
Intros X H'0.
Rewrite (less_than_empty U X H'0); Auto with sets.
Intros; Elim Included_Add with U X A0 x; Auto with sets.
NewDestruct 1 as [A' [H5 H6]].
Rewrite H5; Auto with sets.
Qed.

Lemma Intersection_preserves_finite:
  (A: (Ensemble U)) (Finite U A) ->
   (X: (Ensemble U)) (Finite U (Intersection U X A)).
Proof.
Intros A H' X; Apply Finite_downward_closed with A; Auto with sets.
Qed.

Lemma cardinalO_empty:
  (X: (Ensemble U)) (cardinal U X O) -> X == (Empty_set U).
Proof.
Intros X H; Apply (cardinal_invert U X O); Trivial with sets.
Qed.
Hints Resolve cardinalO_empty.

Lemma inh_card_gt_O:
  (X: (Ensemble U)) (Inhabited U X) -> (n: nat) (cardinal U X n) -> (gt n O).
Proof.
NewInduction 1 as [x H'].
Intros n H'0.
Elim (gt_O_eq n); Auto with sets.
Intro H'1; Generalize H'; Generalize H'0.
Rewrite <- H'1; Intro H'2.
Rewrite (cardinalO_empty X); Auto with sets.
Intro H'3; Elim H'3.
Qed.

Lemma card_soustr_1:
  (X: (Ensemble U)) (n: nat) (cardinal U X n) ->
   (x: U) (In U X x) -> (cardinal U (Subtract U X x) (pred n)).
Proof.
Intros X n H'; Elim H'.
Intros x H'0; Elim H'0.
Clear H' n X.
Intros X n H' H'0 x H'1 x0 H'2.
Elim (classic (In U X x0)).
Intro H'4; Rewrite (add_soustr_xy U X x x0).
Elim (classic x == x0).
Intro H'5.
Absurd (In U X x0); Auto with sets.
Rewrite <- H'5; Auto with sets.
Intro H'3; Try Assumption.
Cut (S (pred n)) = (pred (S n)).
Intro H'5; Rewrite <- H'5.
Apply card_add; Auto with sets.
Red; Intro H'6; Elim H'6.
Intros H'7 H'8; Try Assumption.
Elim H'1; Auto with sets.
Unfold 2 pred; Symmetry.
Apply S_pred with m := O.
Change (gt n O).
Apply inh_card_gt_O with X := X; Auto with sets.
Apply Inhabited_intro with x := x0; Auto with sets.
Red; Intro H'3.
Apply H'1.
Elim H'3; Auto with sets.
Rewrite H'3; Auto with sets.
Elim (classic x == x0).
Intro H'3; Rewrite <- H'3.
Cut (Subtract U (Add U X x) x) == X; Auto with sets.
Intro H'4; Rewrite H'4; Auto with sets.
Intros H'3 H'4; Try Assumption.
Absurd (In U (Add U X x) x0); Auto with sets.
Red; Intro H'5; Try Exact H'5.
LApply (Add_inv U X x x0); Tauto.
Qed.

Lemma cardinal_is_functional:
  (X: (Ensemble U)) (c1: nat) (cardinal U X c1) ->
   (Y: (Ensemble U)) (c2: nat) (cardinal U Y c2) -> X == Y ->
    c1 = c2.
Proof.
Intros X c1 H'; Elim H'.
Intros Y c2 H'0; Elim H'0; Auto with sets.
Intros A n H'1 H'2 x H'3 H'5.
Elim (not_Empty_Add U A x); Auto with sets.
Clear H' c1 X.
Intros X n H' H'0 x H'1 Y c2 H'2.
Elim H'2.
Intro H'3.
Elim (not_Empty_Add U X x); Auto with sets.
Clear H'2 c2 Y.
Intros X0 c2 H'2 H'3 x0 H'4 H'5.
Elim (classic (In U X0 x)).
Intro H'6; Apply f_equal with nat.
Apply H'0 with Y := (Subtract U (Add U X0 x0) x).
ElimType (pred (S c2)) = c2; Auto with sets.
Apply card_soustr_1; Auto with sets.
Rewrite <- H'5.
Apply Sub_Add_new; Auto with sets.
Elim (classic x == x0).
Intros H'6 H'7; Apply f_equal with nat.
Apply H'0 with Y := X0; Auto with sets.
Apply Simplify_add with x := x; Auto with sets.
Pattern 2 x; Rewrite H'6; Auto with sets.
Intros H'6 H'7.
Absurd (Add U X x) == (Add U X0 x0); Auto with sets.
Clear H'0 H' H'3 n H'5 H'4 H'2 H'1 c2.
Red; Intro H'.
LApply (Extension U (Add U X x) (Add U X0 x0)); Auto with sets.
Clear H'.
Intro H'; Red in H'.
Elim H'; Intros H'0 H'1; Red in H'0; Clear H' H'1.
Absurd (In U (Add U X0 x0) x); Auto with sets.
LApply (Add_inv U X0 x0 x); [ Intuition | Apply (H'0 x); Apply Add_intro2 ].
Qed.

Lemma cardinal_Empty : (m:nat)(cardinal U (Empty_set U) m) -> O = m.
Proof.
Intros m Cm; Generalize (cardinal_invert U (Empty_set U) m Cm).
Elim m; Auto with sets.
Intros; Elim H0; Intros; Elim H1; Intros; Elim H2; Intros.
Elim (not_Empty_Add U x x0 H3).
Qed.

Lemma cardinal_unicity :
  (X: (Ensemble U)) (n: nat) (cardinal U X n) -> 
                    (m: nat) (cardinal U X m) -> n = m.
Proof.
Intros; Apply cardinal_is_functional with X X; Auto with sets.
Qed.

Lemma card_Add_gen:
  (A: (Ensemble U))
  (x: U) (n, n': nat) (cardinal U A n) -> (cardinal U (Add U A x) n') ->
   (le n' (S n)).
Proof.
Intros A x n n' H'.
Elim (classic (In U A x)).
Intro H'0.
Rewrite (Non_disjoint_union U A x H'0).
Intro H'1; Cut n = n'.
Intro E; Rewrite E; Auto with sets.
Apply cardinal_unicity with A; Auto with sets.
Intros H'0 H'1.
Cut n'=(S n).
Intro E; Rewrite E; Auto with sets.
Apply cardinal_unicity with (Add U A x); Auto with sets.
Qed.

Lemma incl_st_card_lt:
  (X: (Ensemble U)) (c1: nat) (cardinal U X c1) ->
  (Y: (Ensemble U)) (c2: nat) (cardinal U Y c2) -> (Strict_Included U X Y) ->
    (gt c2 c1).
Proof.
Intros X c1 H'; Elim H'.
Intros Y c2 H'0; Elim H'0; Auto with sets arith.
Intro H'1.
Elim (Strict_Included_strict U (Empty_set U)); Auto with sets arith.
Clear H' c1 X.
Intros X n H' H'0 x H'1 Y c2 H'2.
Elim H'2.
Intro H'3; Elim (not_SIncl_empty U (Add U X x)); Auto with sets arith.
Clear H'2 c2 Y.
Intros X0 c2 H'2 H'3 x0 H'4 H'5; Elim (classic (In U X0 x)).
Intro H'6; Apply gt_n_S.
Apply H'0 with Y := (Subtract U (Add U X0 x0) x).
ElimType (pred (S c2)) = c2; Auto with sets arith.
Apply card_soustr_1; Auto with sets arith.
Apply incl_st_add_soustr; Auto with sets arith.
Elim (classic x == x0).
Intros H'6 H'7; Apply gt_n_S.
Apply H'0 with Y := X0; Auto with sets arith.
Apply sincl_add_x with x := x0.
Rewrite <- H'6; Auto with sets arith.
Pattern 1 x0; Rewrite <- H'6; Trivial with sets arith.
Intros H'6 H'7; Red in H'5.
Elim H'5; Intros H'8 H'9; Try Exact H'8; Clear H'5.
Red in H'8.
Generalize (H'8 x).
Intro H'5; LApply H'5; Auto with sets arith.
Intro H; Elim Add_inv with U X0 x0 x; Auto with sets arith.
Intro; Absurd (In U X0 x); Auto with sets arith.
Intro; Absurd x==x0; Auto with sets arith.
Qed.

Lemma incl_card_le:
  (X,Y: (Ensemble U)) (n,m: nat) (cardinal U X n) -> (cardinal U Y m) -> 
  (Included U X Y) -> (le n m).
Proof.
Intros;
Elim Included_Strict_Included with U X Y; Auto with sets arith; Intro.
Cut (gt m n); Auto with sets arith.
Apply incl_st_card_lt with X := X Y := Y; Auto with sets arith.
Generalize H0; Rewrite <- H2; Intro.
Cut n=m.
Intro E; Rewrite E; Auto with sets arith.
Apply cardinal_unicity with X; Auto with sets arith.
Qed.

Lemma G_aux:
  (P:(Ensemble U) ->Prop)
  ((X:(Ensemble U))
   (Finite U X) -> ((Y:(Ensemble U)) (Strict_Included U Y X) ->(P Y)) ->(P X)) ->
  (P (Empty_set U)).
Proof.
Intros P H'; Try Assumption.
Apply H'; Auto with sets.
Clear H'; Auto with sets.
Intros Y H'; Try Assumption.
Red in H'.
Elim H'; Intros H'0 H'1; Try Exact H'1; Clear H'.
LApply (less_than_empty U Y); [Intro H'3; Try Exact H'3 | Assumption].
Elim H'1; Auto with sets.
Qed.

Hints Unfold  not.

Lemma Generalized_induction_on_finite_sets:
  (P:(Ensemble U) ->Prop)
  ((X:(Ensemble U))
   (Finite U X) -> ((Y:(Ensemble U)) (Strict_Included U Y X) ->(P Y)) ->(P X)) ->
  (X:(Ensemble U)) (Finite U X) ->(P X).
Proof.
Intros P H'0 X H'1.
Generalize P H'0; Clear H'0 P.
Elim H'1.
Intros P H'0.
Apply G_aux; Auto with sets.
Clear H'1 X.
Intros A H' H'0 x H'1 P H'3.
Cut (Y:(Ensemble U)) (Included U Y (Add U A x)) ->(P Y); Auto with sets.
Generalize H'1.
Apply H'0.
Intros X K H'5 L Y H'6; Apply H'3; Auto with sets.
Apply Finite_downward_closed with A := (Add U X x); Auto with sets.
Intros Y0 H'7.
Elim (Strict_inclusion_is_transitive_with_inclusion U Y0 Y (Add U X x)); Auto with sets.
Intros H'2 H'4.
Elim (Included_Add U Y0 X x);
 [Intro H'14 |
   Intro H'14; Elim H'14; Intros A' E; Elim E; Intros H'15 H'16; Clear E H'14 |
   Idtac]; Auto with sets.
Elim (Included_Strict_Included U Y0 X); Auto with sets.
Intro H'9; Apply H'5 with Y := Y0; Auto with sets.
Intro H'9; Rewrite H'9.
Apply H'3; Auto with sets.
Intros Y1 H'8; Elim H'8.
Intros H'10 H'11; Apply H'5 with Y := Y1; Auto with sets.
Elim (Included_Strict_Included U A' X); Auto with sets.
Intro H'8; Apply H'5 with Y := A'; Auto with sets.
Rewrite <- H'15; Auto with sets.
Intro H'8.
Elim H'7.
Intros H'9 H'10; Apply H'10 Orelse Elim H'10; Try Assumption.
Generalize H'6.
Rewrite <- H'8.
Rewrite <- H'15; Auto with sets.
Qed.

End Finite_sets_facts.

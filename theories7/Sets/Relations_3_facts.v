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

Require Export Relations_1.
Require Export Relations_1_facts.
Require Export Relations_2.
Require Export Relations_2_facts.
Require Export Relations_3.

Theorem Rstar_imp_coherent :
  (U: Type) (R: (Relation U)) (x: U) (y: U) (Rstar U R x y) ->
   (coherent U R x y).
Proof.
Intros U R x y H'; Red.
Exists y; Auto with sets.
Qed.
Hints Resolve Rstar_imp_coherent.

Theorem coherent_symmetric :
  (U: Type) (R: (Relation U)) (Symmetric U (coherent U R)).
Proof.
Unfold 1 coherent.
Intros U R; Red.
Intros x y H'; Elim H'.
Intros z H'0; Exists z; Tauto.
Qed.

Theorem Strong_confluence :
  (U: Type) (R: (Relation U)) (Strongly_confluent U R) -> (Confluent U R).
Proof.
Intros U R H'; Red.
Intro x; Red; Intros a b H'0.
Unfold 1 coherent.
Generalize b; Clear b.
Elim H'0; Clear H'0.
Intros x0 b H'1; Exists b; Auto with sets.
Intros x0 y z H'1 H'2 H'3 b H'4.
Generalize (Lemma1 U R); Intro h; LApply h;
  [Intro H'0; Generalize (H'0 x0 b); Intro h0; LApply h0;
    [Intro H'5; Generalize (H'5 y); Intro h1; LApply h1;
      [Intro h2; Elim h2; Intros z0 h3; Elim h3; Intros H'6 H'7;
        Clear h h0 h1 h2 h3 | Clear h h0 h1] | Clear h h0] | Clear h]; Auto with sets.
Generalize (H'3 z0); Intro h; LApply h;
  [Intro h0; Elim h0; Intros z1 h1; Elim h1; Intros H'8 H'9; Clear h h0 h1 |
    Clear h]; Auto with sets.
Exists z1; Split; Auto with sets.
Apply Rstar_n with z0; Auto with sets.
Qed.

Theorem Strong_confluence_direct :
  (U: Type) (R: (Relation U)) (Strongly_confluent U R) -> (Confluent U R).
Proof.
Intros U R H'; Red.
Intro x; Red; Intros a b H'0.
Unfold 1 coherent.
Generalize b; Clear b.
Elim H'0; Clear H'0.
Intros x0 b H'1; Exists b; Auto with sets.
Intros x0 y z H'1 H'2 H'3 b H'4.
Cut (exT U [t: U] (Rstar U R y t) /\ (R b t)).
Intro h; Elim h; Intros t h0; Elim h0; Intros H'0 H'5; Clear h h0.
Generalize (H'3 t); Intro h; LApply h;
  [Intro h0; Elim h0; Intros z0 h1; Elim h1; Intros H'6 H'7; Clear h h0 h1 |
    Clear h]; Auto with sets.
Exists z0; Split; [Assumption | Idtac].
Apply Rstar_n with t; Auto with sets.
Generalize H'1; Generalize y; Clear H'1.
Elim H'4.
Intros x1 y0 H'0; Exists y0; Auto with sets.
Intros x1 y0 z0 H'0 H'1 H'5 y1 H'6.
Red in H'.
Generalize (H' x1 y0 y1); Intro h; LApply h;
  [Intro H'7; LApply H'7;
    [Intro h0; Elim h0; Intros z1 h1; Elim h1; Intros H'8 H'9; Clear h H'7 h0 h1 |
      Clear h] | Clear h]; Auto with sets.
Generalize (H'5 z1); Intro h; LApply h;
  [Intro h0; Elim h0; Intros t h1; Elim h1; Intros H'7 H'10; Clear h h0 h1 |
    Clear h]; Auto with sets.
Exists t; Split; Auto with sets.
Apply Rstar_n with z1; Auto with sets.
Qed.

Theorem Noetherian_contains_Noetherian :
  (U: Type) (R, R': (Relation U)) (Noetherian U R) -> (contains U R R') ->
   (Noetherian U R').
Proof.
Unfold 2 Noetherian.
Intros U R R' H' H'0 x.
Elim (H' x); Auto with sets.
Qed.

Theorem Newman :
  (U: Type) (R: (Relation U)) (Noetherian U R) -> (Locally_confluent U R) ->
   (Confluent U R).
Proof.
Intros U R H' H'0; Red; Intro x.
Elim (H' x); Unfold confluent.
Intros x0 H'1 H'2 y z H'3 H'4.
Generalize (Rstar_cases U R x0 y); Intro h; LApply h;
  [Intro h0; Elim h0;
    [Clear h h0; Intro h1 |
      Intro h1; Elim h1; Intros u h2; Elim h2; Intros H'5 H'6; Clear h h0 h1 h2] |
    Clear h]; Auto with sets.
Elim h1; Auto with sets.
Generalize (Rstar_cases U R x0 z); Intro h; LApply h;
  [Intro h0; Elim h0;
    [Clear h h0; Intro h1 |
      Intro h1; Elim h1; Intros v h2; Elim h2; Intros H'7 H'8; Clear h h0 h1 h2] |
    Clear h]; Auto with sets.
Elim h1; Generalize coherent_symmetric; Intro t; Red in t; Auto with sets.
Unfold Locally_confluent locally_confluent coherent in H'0.
Generalize (H'0 x0 u v); Intro h; LApply h;
  [Intro H'9; LApply H'9;
    [Intro h0; Elim h0; Intros t h1; Elim h1; Intros H'10 H'11;
      Clear h H'9 h0 h1 | Clear h] | Clear h]; Auto with sets.
Clear H'0.
Unfold 1 coherent in H'2.
Generalize (H'2 u); Intro h; LApply h;
  [Intro H'0; Generalize (H'0 y t); Intro h0; LApply h0;
    [Intro H'9; LApply H'9;
      [Intro h1; Elim h1; Intros y1 h2; Elim h2; Intros H'12 H'13;
        Clear h h0 H'9 h1 h2 | Clear h h0] | Clear h h0] | Clear h]; Auto with sets.
Generalize Rstar_transitive; Intro T; Red in T.
Generalize (H'2 v); Intro h; LApply h;
  [Intro H'9; Generalize (H'9 y1 z); Intro h0; LApply h0;
    [Intro H'14; LApply H'14;
      [Intro h1; Elim h1; Intros z1 h2; Elim h2; Intros H'15 H'16;
        Clear h h0 H'14 h1 h2 | Clear h h0] | Clear h h0] | Clear h]; Auto with sets.
Red; (Exists z1; Split); Auto with sets.
Apply T with y1; Auto with sets.
Apply T with t; Auto with sets.
Qed.

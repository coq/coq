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

Theorem Rstar_reflexive : 
  (U: Type) (R: (Relation U)) (Reflexive U (Rstar U R)).
Proof.
Auto with sets.
Qed.

Theorem Rplus_contains_R :
  (U: Type) (R: (Relation U)) (contains U (Rplus U R) R).
Proof.
Auto with sets.
Qed.

Theorem Rstar_contains_R :
  (U: Type) (R: (Relation U)) (contains U (Rstar U R) R).
Proof.
Intros U R; Red; Intros x y H'; Apply Rstar_n with y; Auto with sets.
Qed.

Theorem Rstar_contains_Rplus :
  (U: Type) (R: (Relation U)) (contains U (Rstar U R) (Rplus U R)).
Proof.
Intros U R; Red.
Intros x y H'; Elim H'.
Generalize Rstar_contains_R; Intro T; Red in T; Auto with sets.
Intros x0 y0 z H'0 H'1 H'2; Apply Rstar_n with y0; Auto with sets.
Qed.

Theorem Rstar_transitive :
  (U: Type) (R: (Relation U)) (Transitive U (Rstar U R)).
Proof.
Intros U R; Red.
Intros x y z H'; Elim H'; Auto with sets.
Intros x0 y0 z0 H'0 H'1 H'2 H'3; Apply Rstar_n with y0; Auto with sets.
Qed.

Theorem Rstar_cases :
  (U: Type) (R: (Relation U)) (x, y: U) (Rstar U R x y) ->
    x == y \/ (EXT u | (R x u) /\ (Rstar U R u y)).
Proof.
Intros U R x y H'; Elim H'; Auto with sets.
Intros x0 y0 z H'0 H'1 H'2; Right; Exists y0; Auto with sets.
Qed.

Theorem Rstar_equiv_Rstar1 :
  (U: Type) (R: (Relation U)) (same_relation U (Rstar U R) (Rstar1 U R)).
Proof.
Generalize Rstar_contains_R; Intro T; Red in T.
Intros U R; Unfold same_relation contains.
Split; Intros x y H'; Elim H'; Auto with sets.
Generalize Rstar_transitive; Intro T1; Red in T1.
Intros x0 y0 z H'0 H'1 H'2 H'3; Apply T1 with y0; Auto with sets.
Intros x0 y0 z H'0 H'1 H'2; Apply Rstar1_n with y0; Auto with sets.
Qed.

Theorem Rsym_imp_Rstarsym :
  (U: Type) (R: (Relation U)) (Symmetric U R) -> (Symmetric U (Rstar U R)).
Proof.
Intros U R H'; Red.
Intros x y H'0; Elim H'0; Auto with sets.
Intros x0 y0 z H'1 H'2 H'3.
Generalize Rstar_transitive; Intro T1; Red in T1.
Apply T1 with y0; Auto with sets.
Apply Rstar_n with x0; Auto with sets.
Qed.

Theorem Sstar_contains_Rstar :
  (U: Type) (R, S: (Relation U)) (contains U (Rstar U S) R) ->
   (contains U (Rstar U S) (Rstar U R)).
Proof.
Unfold contains.
Intros U R S H' x y H'0; Elim H'0; Auto with sets.
Generalize Rstar_transitive; Intro T1; Red in T1.
Intros x0 y0 z H'1 H'2 H'3; Apply T1 with y0; Auto with sets.
Qed.

Theorem star_monotone :
  (U: Type) (R, S: (Relation U)) (contains U S R) ->
   (contains U (Rstar U S) (Rstar U R)).
Proof.
Intros U R S H'.
Apply Sstar_contains_Rstar; Auto with sets.
Generalize (Rstar_contains_R U S); Auto with sets.
Qed.

Theorem RstarRplus_RRstar :
  (U: Type) (R: (Relation U)) (x, y, z: U) 
    (Rstar U R x y) -> (Rplus U R y z) ->
    (EXT u | (R x u) /\ (Rstar U R u z)).
Proof.
Generalize Rstar_contains_Rplus; Intro T; Red in T.
Generalize Rstar_transitive; Intro T1; Red in T1.
Intros U R x y z H'; Elim H'.
Intros x0 H'0; Elim H'0.
Intros x1 y0 H'1; Exists y0; Auto with sets.
Intros x1 y0 z0 H'1 H'2 H'3; Exists y0; Auto with sets.
Intros x0 y0 z0 H'0 H'1 H'2 H'3; Exists y0.
Split; [Try Assumption | Idtac].
Apply T1 with z0; Auto with sets.
Qed.

Theorem Lemma1 : 
  (U: Type) (R: (Relation U)) (Strongly_confluent U R) ->
   (x, b: U) (Rstar U R x b) ->
    (a: U) (R x a) -> (EXT z | (Rstar U R a z) /\ (R b z)).
Proof.
Intros U R H' x b H'0; Elim H'0.
Intros x0 a H'1; Exists a; Auto with sets.
Intros x0 y z H'1 H'2 H'3 a H'4.
Red in H'.
Specialize 3 H' with x := x0 a := a b := y; Intro H'7; LApply H'7;
 [Intro H'8; LApply H'8;
   [Intro H'9; Try Exact H'9; Clear H'8 H'7 | Clear H'8 H'7] | Clear H'7]; Auto with sets.
Elim H'9.
Intros t H'5; Elim H'5; Intros H'6 H'7; Try Exact H'6; Clear H'5.
Elim (H'3 t); Auto with sets.
Intros z1 H'5; Elim H'5; Intros H'8 H'10; Try Exact H'8; Clear H'5.
Exists z1; Split; [Idtac | Assumption].
Apply Rstar_n with t; Auto with sets.
Qed.

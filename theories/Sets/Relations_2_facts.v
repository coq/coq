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

Require Export Relations_1.
Require Export Relations_1_facts.
Require Export Relations_2.

Theorem Rstar_reflexive :
 forall (U:Type) (R:Relation U), Reflexive U (Rstar U R).
Proof.
auto with sets.
Qed.

Theorem Rplus_contains_R :
 forall (U:Type) (R:Relation U), contains U (Rplus U R) R.
Proof.
auto with sets.
Qed.

Theorem Rstar_contains_R :
 forall (U:Type) (R:Relation U), contains U (Rstar U R) R.
Proof.
intros U R; red; intros x y H'; apply Rstar_n with y; auto with sets.
Qed.

Theorem Rstar_contains_Rplus :
 forall (U:Type) (R:Relation U), contains U (Rstar U R) (Rplus U R).
Proof.
intros U R; red.
intros x y H'; elim H'.
generalize Rstar_contains_R; intro T; red in T; auto with sets.
intros x0 y0 z H'0 H'1 H'2; apply Rstar_n with y0; auto with sets.
Qed.

Theorem Rstar_transitive :
 forall (U:Type) (R:Relation U), Transitive U (Rstar U R).
Proof.
intros U R; red.
intros x y z H'; elim H'; auto with sets.
intros x0 y0 z0 H'0 H'1 H'2 H'3; apply Rstar_n with y0; auto with sets.
Qed.

Theorem Rstar_cases :
 forall (U:Type) (R:Relation U) (x y:U),
   Rstar U R x y -> x = y \/ (exists u : _, R x u /\ Rstar U R u y).
Proof.
intros U R x y H'; elim H'; auto with sets.
intros x0 y0 z H'0 H'1 H'2; right; exists y0; auto with sets.
Qed.

Theorem Rstar_equiv_Rstar1 :
 forall (U:Type) (R:Relation U), same_relation U (Rstar U R) (Rstar1 U R).
Proof.
generalize Rstar_contains_R; intro T; red in T.
intros U R; unfold same_relation, contains.
split; intros x y H'; elim H'; auto with sets.
generalize Rstar_transitive; intro T1; red in T1.
intros x0 y0 z H'0 H'1 H'2 H'3; apply T1 with y0; auto with sets.
intros x0 y0 z H'0 H'1 H'2; apply Rstar1_n with y0; auto with sets.
Qed.

Theorem Rsym_imp_Rstarsym :
 forall (U:Type) (R:Relation U), Symmetric U R -> Symmetric U (Rstar U R).
Proof.
intros U R H'; red.
intros x y H'0; elim H'0; auto with sets.
intros x0 y0 z H'1 H'2 H'3.
generalize Rstar_transitive; intro T1; red in T1.
apply T1 with y0; auto with sets.
apply Rstar_n with x0; auto with sets.
Qed.

Theorem Sstar_contains_Rstar :
 forall (U:Type) (R S:Relation U),
   contains U (Rstar U S) R -> contains U (Rstar U S) (Rstar U R).
Proof.
unfold contains.
intros U R S H' x y H'0; elim H'0; auto with sets.
generalize Rstar_transitive; intro T1; red in T1.
intros x0 y0 z H'1 H'2 H'3; apply T1 with y0; auto with sets.
Qed.

Theorem star_monotone :
 forall (U:Type) (R S:Relation U),
   contains U S R -> contains U (Rstar U S) (Rstar U R).
Proof.
intros U R S H'.
apply Sstar_contains_Rstar; auto with sets.
generalize (Rstar_contains_R U S); auto with sets.
Qed.

Theorem RstarRplus_RRstar :
 forall (U:Type) (R:Relation U) (x y z:U),
   Rstar U R x y -> Rplus U R y z ->  exists u : _, R x u /\ Rstar U R u z.
Proof.
generalize Rstar_contains_Rplus; intro T; red in T.
generalize Rstar_transitive; intro T1; red in T1.
intros U R x y z H'; elim H'.
intros x0 H'0; elim H'0.
intros x1 y0 H'1; exists y0; auto with sets.
intros x1 y0 z0 H'1 H'2 H'3; exists y0; auto with sets.
intros x0 y0 z0 H'0 H'1 H'2 H'3; exists y0.
split; [ try assumption | idtac ].
apply T1 with z0; auto with sets.
Qed.

Theorem Lemma1 :
 forall (U:Type) (R:Relation U),
   Strongly_confluent U R ->
   forall x b:U,
     Rstar U R x b ->
     forall a:U, R x a ->  exists z : _, Rstar U R a z /\ R b z.
Proof.
intros U R H' x b H'0; elim H'0.
intros x0 a H'1; exists a; auto with sets.
intros x0 y z H'1 H'2 H'3 a H'4.
red in H'.
specialize H' with (x := x0) (a := a) (b := y); lapply H';
 [ intro H'8; lapply H'8;
    [ intro H'9; try exact H'9; clear H'8 H' | clear H'8 H' ]
 | clear H' ]; auto with sets.
elim H'9.
intros t H'5; elim H'5; intros H'6 H'7; try exact H'6; clear H'5.
elim (H'3 t); auto with sets.
intros z1 H'5; elim H'5; intros H'8 H'10; try exact H'8; clear H'5.
exists z1; split; [ idtac | assumption ].
apply Rstar_n with t; auto with sets.
Qed.

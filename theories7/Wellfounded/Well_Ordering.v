(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Author: Cristina Cornes.
    From: Constructing Recursion Operators in Type Theory
    L. Paulson  JSC (1986) 2, 325-355 *)

Require Eqdep.

Section WellOrdering.
Variable A:Set.
Variable B:A->Set. 

Inductive WO : Set :=
   sup : (a:A)(f:(B a)->WO)WO.


Inductive le_WO  : WO->WO->Prop :=
  le_sup : (a:A)(f:(B a)->WO)(v:(B a)) (le_WO  (f v) (sup a f)).
 

Theorem wf_WO : (well_founded WO le_WO ).
Proof.
 Unfold well_founded ;Intro.
 Apply Acc_intro.
 Elim a.
 Intros.
 Inversion H0.
 Apply Acc_intro.
 Generalize H4 ;Generalize H1 ;Generalize f0 ;Generalize v.
 Rewrite -> H3.
 Intros.
 Apply (H v0 y0).
 Cut (eq ? f f1).
 Intros E;Rewrite -> E;Auto.
 Symmetry.
 Apply (inj_pair2 A [a0:A](B a0)->WO a0 f1 f H5).
Qed.

End WellOrdering.


Section Characterisation_wf_relations.

(** Wellfounded relations are the inverse image of wellordering types *)
(*  in course of development                                          *)


Variable A:Set.
Variable leA:A->A->Prop.

Definition B:= [a:A] {x:A | (leA x a)}.

Definition  wof: (well_founded A leA)-> A-> (WO A B).
Proof.
 Intros.
 Apply (well_founded_induction A leA H [a:A](WO A B));Auto.
 Intros.
 Apply (sup A B x).
 Unfold 1 B .
 NewDestruct 1 as [x0].
 Apply (H1 x0);Auto.
Qed.

End Characterisation_wf_relations.

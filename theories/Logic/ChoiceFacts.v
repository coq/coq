(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(* We show that the functional formulation of the axiom of Choice
   (usual formulation in type theory) is equivalent to its relational
   formulation (only formulation of set theory) + the axiom of
   (parametric) definite description (aka axiom of unique choice) *)

(* This shows that the axiom of choice can be assumed (under its
   relational formulation) without known inconsistency with classical logic,
   though definite description conflicts with classical logic *)

Definition RelationalChoice :=
 (A:Type;B:Type;R: A->B->Prop) 
  ((x:A)(EX y:B|(R x y)))
   -> (EXT R':A->B->Prop | 
         ((x:A)(EX y:B|(R x y)/\(R' x y)/\ ((y':B) (R' x y') -> y=y')))).

Definition FunctionalChoice :=
 (A:Type;B:Type;R: A->B->Prop)
  ((x:A)(EX y:B|(R x y))) -> (EX f:A->B | (x:A)(R x (f x))).

Definition ParamDefiniteDescription :=
 (A:Type;B:Type;R: A->B->Prop)
  ((x:A)(EX y:B|(R x y)/\ ((y':B)(R x y') -> y=y')))
   -> (EX f:A->B | (x:A)(R x (f x))).

Lemma description_rel_choice_imp_funct_choice : 
  ParamDefiniteDescription->RelationalChoice->FunctionalChoice.
Intros Descr RelCh.
Red; Intros A B R H.
NewDestruct (RelCh A B R H) as [R' H0].
NewDestruct (Descr A B R') as [f H1].
Intro x.
Elim (H0 x); Intros y [H2 [H3 H4]]; Exists y; Split; [Exact H3 | Exact H4].
Exists f; Intro x.
Elim (H0 x); Intros y [H2 [H3 H4]].
Rewrite <- (H4 (f x) (H1 x)).
Exact H2.
Qed.

Lemma funct_choice_imp_rel_choice : 
  FunctionalChoice->RelationalChoice.
Intros FunCh.
Red; Intros A B R H.
NewDestruct (FunCh A B R H) as [f H0].
Exists [x,y]y=(f x).
Intro x; Exists (f x);
Split; [Apply H0| Split;[Reflexivity| Intros y H1; Symmetry; Exact H1]].
Qed.

Lemma funct_choice_imp_description : 
  FunctionalChoice->ParamDefiniteDescription.
Intros FunCh.
Red; Intros A B R H.
NewDestruct (FunCh A B R) as [f H0].
(* 1 *)
Intro x.
Elim (H x); Intros y [H0 H1].
Exists y; Exact H0.
(* 2 *)
Exists f; Exact H0.
Qed.

Theorem FunChoice_Equiv_RelChoice_and_ParamDefinDescr :
  FunctionalChoice <-> RelationalChoice /\ ParamDefiniteDescription.
Split.
Intro H; Split; [
  Exact (funct_choice_imp_rel_choice H)
 | Exact (funct_choice_imp_description H)].
Intros [H H0]; Exact (description_rel_choice_imp_funct_choice H0 H).
Qed.

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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

(* We show that the guarded relational formulation of the axiom of Choice
   comes from the non guarded formulation in presence either of the
   independance of premises or proof-irrelevance *)

Definition GuardedRelationalChoice :=
 (A:Type;B:Type;P:A->Prop;R: A->B->Prop) 
  ((x:A)(P x)->(EX y:B|(R x y)))
   -> (EXT R':A->B->Prop | 
        ((x:A)(P x)->(EX y:B|(R x y)/\(R' x y)/\ ((y':B) (R' x y') -> y=y')))).

Definition ProofIrrelevance := (A:Prop)(a1,a2:A) a1==a2.

Lemma rel_choice_and_proof_irrel_imp_guarded_rel_choice : 
  RelationalChoice -> ProofIrrelevance -> GuardedRelationalChoice.
Proof.
Intros rel_choice proof_irrel.
Red; Intros A B P R H.
NewDestruct (rel_choice ? ? [x:(sigT ? P);y:B](R (projT1 ? ? x) y)) as [R' H0].
Intros [x HPx].
NewDestruct (H x HPx) as [y HRxy].
Exists y; Exact HRxy.
Pose R'':=[x:A;y:B](EXT H:(P x) | (R' (existT ? P x H) y)).
Exists R''; Intros x HPx.
NewDestruct (H0 (existT ? P x HPx)) as [y [HRxy [HR'xy Huniq]]].
Exists y. Split.
  Exact HRxy.
  Split.
    Red; Exists HPx; Exact HR'xy.
    Intros y' HR''xy'.
      Apply Huniq.
      Unfold R'' in HR''xy'.
      NewDestruct HR''xy' as [H'Px HR'xy'].
      Rewrite proof_irrel with a1:=HPx a2:=H'Px.
      Exact HR'xy'.
Qed.

Definition IndependenceOfPremises :=
 (A:Type)(P:A->Prop)(Q:Prop)(Q->(EXT x|(P x)))->(EXT x|Q->(P x)).

Lemma rel_choice_indep_of_premises_imp_guarded_rel_choice :
  RelationalChoice -> IndependenceOfPremises -> GuardedRelationalChoice.
Proof.
Intros RelCh IndPrem.
Red; Intros A B P R H.
NewDestruct (RelCh A B [x,y](P x)->(R x y)) as [R' H0].
  Intro x. Apply IndPrem.
    Apply H.
  Exists R'.
  Intros x HPx.
    NewDestruct (H0 x) as [y [H1 H2]].
    Exists y. Split. 
      Apply (H1 HPx).
      Exact H2.
Qed.

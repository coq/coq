(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** We show that the functional formulation of the axiom of Choice
   (usual formulation in type theory) is equivalent to its relational
   formulation (only formulation of set theory) + the axiom of
   (parametric) definite description (aka axiom of unique choice) *)

(** This shows that the axiom of choice can be assumed (under its
   relational formulation) without known inconsistency with classical logic,
   though definite description conflicts with classical logic *)

Definition RelationalChoice :=
  forall (A B:Type) (R:A -> B -> Prop),
    (forall x:A,  exists y : B, R x y) ->
     exists R' : A -> B -> Prop,
      (forall x:A,
          exists y : B, R x y /\ R' x y /\ (forall y':B, R' x y' -> y = y')).

Definition FunctionalChoice :=
  forall (A B:Type) (R:A -> B -> Prop),
    (forall x:A,  exists y : B, R x y) ->
     exists f : A -> B, (forall x:A, R x (f x)).

Definition ParamDefiniteDescription :=
  forall (A B:Type) (R:A -> B -> Prop),
    (forall x:A,  exists y : B, R x y /\ (forall y':B, R x y' -> y = y')) ->
     exists f : A -> B, (forall x:A, R x (f x)).

Lemma description_rel_choice_imp_funct_choice :
 ParamDefiniteDescription -> RelationalChoice -> FunctionalChoice.
intros Descr RelCh.
red in |- *; intros A B R H.
destruct (RelCh A B R H) as [R' H0].
destruct (Descr A B R') as [f H1].
intro x.
elim (H0 x); intros y [H2 [H3 H4]]; exists y; split; [ exact H3 | exact H4 ].
exists f; intro x.
elim (H0 x); intros y [H2 [H3 H4]].
rewrite <- (H4 (f x) (H1 x)).
exact H2.
Qed.

Lemma funct_choice_imp_rel_choice : FunctionalChoice -> RelationalChoice.
intros FunCh.
red in |- *; intros A B R H.
destruct (FunCh A B R H) as [f H0].
exists (fun x y => y = f x).
intro x; exists (f x); split;
 [ apply H0
 | split; [ reflexivity | intros y H1; symmetry  in |- *; exact H1 ] ].
Qed.

Lemma funct_choice_imp_description :
 FunctionalChoice -> ParamDefiniteDescription.
intros FunCh.
red in |- *; intros A B R H.
destruct (FunCh A B R) as [f H0].
(* 1 *)
intro x.
elim (H x); intros y [H0 H1].
exists y; exact H0.
(* 2 *)
exists f; exact H0.
Qed.

Theorem FunChoice_Equiv_RelChoice_and_ParamDefinDescr :
 FunctionalChoice <-> RelationalChoice /\ ParamDefiniteDescription.
split.
intro H; split;
 [ exact (funct_choice_imp_rel_choice H)
 | exact (funct_choice_imp_description H) ].
intros [H H0]; exact (description_rel_choice_imp_funct_choice H0 H).
Qed.

(** We show that the guarded relational formulation of the axiom of Choice
   comes from the non guarded formulation in presence either of the
   independance of premises or proof-irrelevance *)

Definition GuardedRelationalChoice :=
  forall (A B:Type) (P:A -> Prop) (R:A -> B -> Prop),
    (forall x:A, P x ->  exists y : B, R x y) ->
     exists R' : A -> B -> Prop,
      (forall x:A,
         P x ->
          exists y : B, R x y /\ R' x y /\ (forall y':B, R' x y' -> y = y')).

Definition ProofIrrelevance := forall (A:Prop) (a1 a2:A), a1 = a2.

Lemma rel_choice_and_proof_irrel_imp_guarded_rel_choice :
 RelationalChoice -> ProofIrrelevance -> GuardedRelationalChoice.
Proof.
intros rel_choice proof_irrel.
red in |- *; intros A B P R H.
destruct (rel_choice _ _ (fun (x:sigT P) (y:B) => R (projT1 x) y)) as [R' H0].
intros [x HPx].
destruct (H x HPx) as [y HRxy].
exists y; exact HRxy.
set (R'' := fun (x:A) (y:B) =>  exists H : P x, R' (existT P x H) y).
exists R''; intros x HPx.
destruct (H0 (existT P x HPx)) as [y [HRxy [HR'xy Huniq]]].
exists y. split.
  exact HRxy.
  split.
    red in |- *; exists HPx; exact HR'xy.
    intros y' HR''xy'.
      apply Huniq.
      unfold R'' in HR''xy'.
      destruct HR''xy' as [H'Px HR'xy'].
      rewrite proof_irrel with (a1 := HPx) (a2 := H'Px).
      exact HR'xy'.
Qed.

Definition IndependenceOfPremises :=
  forall (A:Type) (P:A -> Prop) (Q:Prop),
    (Q ->  exists x : _, P x) ->  exists x : _, Q -> P x.

Lemma rel_choice_indep_of_premises_imp_guarded_rel_choice :
 RelationalChoice -> IndependenceOfPremises -> GuardedRelationalChoice.
Proof.
intros RelCh IndPrem.
red in |- *; intros A B P R H.
destruct (RelCh A B (fun x y => P x -> R x y)) as [R' H0].
  intro x. apply IndPrem.
    apply H.
  exists R'.
  intros x HPx.
    destruct (H0 x) as [y [H1 H2]].
    exists y. split. 
      apply (H1 HPx).
      exact H2.
Qed.

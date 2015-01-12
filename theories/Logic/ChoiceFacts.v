(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Some facts and definitions concerning choice and description in
       intuitionistic logic.

We investigate the relations between the following choice and
description principles

- AC_rel  = relational form of the (non extensional) axiom of choice
            (a "set-theoretic" axiom of choice)
- AC_fun  = functional form of the (non extensional) axiom of choice
            (a "type-theoretic" axiom of choice)
- DC_fun  = functional form of the dependent axiom of choice
- ACw_fun = functional form of the countable axiom of choice
- AC!     = functional relation reification
            (known as axiom of unique choice in topos theory,
             sometimes called principle of definite description in
             the context of constructive type theory)

- GAC_rel = guarded relational form of the (non extensional) axiom of choice
- GAC_fun = guarded functional form of the (non extensional) axiom of choice
- GAC!    = guarded functional relation reification

- OAC_rel = "omniscient" relational form of the (non extensional) axiom of choice
- OAC_fun = "omniscient" functional form of the (non extensional) axiom of choice
            (called AC* in Bell [[Bell]])
- OAC!

- ID_iota    = intuitionistic definite description
- ID_epsilon = intuitionistic indefinite description

- D_iota     = (weakly classical) definite description principle
- D_epsilon  = (weakly classical) indefinite description principle

- PI      = proof irrelevance
- IGP     = independence of general premises
            (an unconstrained generalisation of the constructive principle of
             independence of premises)
- Drinker = drinker's paradox (small form)
            (called Ex in Bell [[Bell]])

We let also

- IPL_2   = 2nd-order impredicative minimal predicate logic (with ex. quant.)
- IPL^2   = 2nd-order functional minimal predicate logic (with ex. quant.)
- IPL_2^2 = 2nd-order impredicative, 2nd-order functional minimal pred. logic (with ex. quant.)

with no prerequisite on the non-emptiness of domains

Table of contents

1. Definitions

2. IPL_2^2 |- AC_rel + AC! = AC_fun

3.1. typed IPL_2 + Sigma-types + PI |- AC_rel = GAC_rel  and  IPL_2 |- AC_rel + IGP -> GAC_rel and IPL_2 |- GAC_rel = OAC_rel

3.2. IPL^2 |- AC_fun + IGP = GAC_fun = OAC_fun = AC_fun + Drinker

3.3. D_iota -> ID_iota  and  D_epsilon <-> ID_epsilon + Drinker

4. Derivability of choice for decidable relations with well-ordered codomain

5. Equivalence of choices on dependent or non dependent functional types

6. Non contradiction of constructive descriptions wrt functional choices

7. Definite description transports classical logic to the computational world

8. Choice -> Dependent choice -> Countable choice

References:

[[Bell]] John L. Bell, Choice principles in intuitionistic set theory,
unpublished.

[[Bell93]] John L. Bell, Hilbert's Epsilon Operator in Intuitionistic
Type Theories, Mathematical Logic Quarterly, volume 39, 1993.

[[Carlström05]] Jesper Carlström, Interpreting descriptions in
intentional type theory, Journal of Symbolic Logic 70(2):488-514, 2005.
*)

Set Implicit Arguments.
Local Unset Intuition Negation Unfolding.

(**********************************************************************)
(** * Definitions *)

(** Choice, reification and description schemes *)

(** We make them all polymorphic. Most of them have existentials as conclusion
    so they require polymorphism otherwise their first application (e.g. to an
    existential in [Set]) will fix the level of [A].
*)
(* Set Universe Polymorphism. *)

Section ChoiceSchemes.

Variables A B :Type.

Variable P:A->Prop.

Variable R:A->B->Prop.

(** ** Constructive choice and description *)

(** AC_rel *)

Definition RelationalChoice_on :=
  forall R:A->B->Prop,
    (forall x : A, exists y : B, R x y) ->
    (exists R' : A->B->Prop, subrelation R' R /\ forall x, exists! y, R' x y).

(** AC_fun *)

Definition FunctionalChoice_on :=
  forall R:A->B->Prop,
    (forall x : A, exists y : B, R x y) ->
    (exists f : A->B, forall x : A, R x (f x)).

(** DC_fun *)

Definition FunctionalDependentChoice_on :=
  forall (R:A->A->Prop),
    (forall x, exists y, R x y) -> forall x0,
    (exists f : nat -> A, f 0 = x0 /\ forall n, R (f n) (f (S n))).

(** ACw_fun *)

Definition FunctionalCountableChoice_on :=
  forall (R:nat->A->Prop),
    (forall n, exists y, R n y) ->
    (exists f : nat -> A, forall n, R n (f n)).

(** AC! or Functional Relation Reification (known as Axiom of Unique Choice
    in topos theory; also called principle of definite description *)

Definition FunctionalRelReification_on :=
  forall R:A->B->Prop,
    (forall x : A, exists! y : B, R x y) ->
    (exists f : A->B, forall x : A, R x (f x)).

(** ID_epsilon (constructive version of indefinite description;
    combined with proof-irrelevance, it may be connected to
    Carlström's type theory with a constructive indefinite description
    operator) *)

Definition ConstructiveIndefiniteDescription_on :=
  forall P:A->Prop,
    (exists x, P x) -> { x:A | P x }.

(** ID_iota (constructive version of definite description; combined
    with proof-irrelevance, it may be connected to Carlström's and
    Stenlund's type theory with a constructive definite description
    operator) *)

Definition ConstructiveDefiniteDescription_on :=
  forall P:A->Prop,
    (exists! x, P x) -> { x:A | P x }.

(** ** Weakly classical choice and description *)

(** GAC_rel *)

Definition GuardedRelationalChoice_on :=
  forall P : A->Prop, forall R : A->B->Prop,
    (forall x : A, P x -> exists y : B, R x y) ->
    (exists R' : A->B->Prop,
      subrelation R' R /\ forall x, P x -> exists! y, R' x y).

(** GAC_fun *)

Definition GuardedFunctionalChoice_on :=
  forall P : A->Prop, forall R : A->B->Prop,
    inhabited B ->
    (forall x : A, P x -> exists y : B, R x y) ->
    (exists f : A->B, forall x, P x -> R x (f x)).

(** GFR_fun *)

Definition GuardedFunctionalRelReification_on :=
  forall P : A->Prop, forall R : A->B->Prop,
    inhabited B ->
    (forall x : A, P x -> exists! y : B, R x y) ->
    (exists f : A->B, forall x : A, P x -> R x (f x)).

(** OAC_rel *)

Definition OmniscientRelationalChoice_on :=
  forall R : A->B->Prop,
    exists R' : A->B->Prop,
      subrelation R' R /\ forall x : A, (exists y : B, R x y) -> exists! y, R' x y.

(** OAC_fun *)

Definition OmniscientFunctionalChoice_on :=
  forall R : A->B->Prop,
    inhabited B ->
    exists f : A->B, forall x : A, (exists y : B, R x y) -> R x (f x).

(** D_epsilon *)

Definition EpsilonStatement_on :=
  forall P:A->Prop,
    inhabited A -> { x:A | (exists x, P x) -> P x }.

(** D_iota *)

Definition IotaStatement_on :=
  forall P:A->Prop,
    inhabited A -> { x:A | (exists! x, P x) -> P x }.

End ChoiceSchemes.

(** Generalized schemes *)

Notation RelationalChoice :=
  (forall A B : Type, RelationalChoice_on A B).
Notation FunctionalChoice :=
  (forall A B : Type, FunctionalChoice_on A B).
Definition FunctionalDependentChoice :=
  (forall A : Type, FunctionalDependentChoice_on A).
Definition FunctionalCountableChoice :=
  (forall A : Type, FunctionalCountableChoice_on A).
Notation FunctionalChoiceOnInhabitedSet :=
  (forall A B : Type, inhabited B -> FunctionalChoice_on A B).
Notation FunctionalRelReification :=
  (forall A B : Type, FunctionalRelReification_on A B).

Notation GuardedRelationalChoice :=
  (forall A B : Type, GuardedRelationalChoice_on A B).
Notation GuardedFunctionalChoice :=
  (forall A B : Type, GuardedFunctionalChoice_on A B).
Notation GuardedFunctionalRelReification :=
  (forall A B : Type, GuardedFunctionalRelReification_on A B).

Notation OmniscientRelationalChoice :=
  (forall A B : Type, OmniscientRelationalChoice_on A B).
Notation OmniscientFunctionalChoice :=
  (forall A B : Type, OmniscientFunctionalChoice_on A B).

Notation ConstructiveDefiniteDescription :=
  (forall A : Type, ConstructiveDefiniteDescription_on A).
Notation ConstructiveIndefiniteDescription :=
  (forall A : Type, ConstructiveIndefiniteDescription_on A).

Notation IotaStatement :=
  (forall A : Type, IotaStatement_on A).
Notation EpsilonStatement :=
  (forall A : Type, EpsilonStatement_on A).

(** Subclassical schemes *)

Definition ProofIrrelevance :=
  forall (A:Prop) (a1 a2:A), a1 = a2.

Definition IndependenceOfGeneralPremises :=
  forall (A:Type) (P:A -> Prop) (Q:Prop),
    inhabited A ->
    (Q -> exists x, P x) -> exists x, Q -> P x.

Definition SmallDrinker'sParadox :=
  forall (A:Type) (P:A -> Prop), inhabited A ->
    exists x, (exists x, P x) -> P x.

(**********************************************************************)
(** * AC_rel + AC! = AC_fun

   We show that the functional formulation of the axiom of Choice
   (usual formulation in type theory) is equivalent to its relational
   formulation (only formulation of set theory) + functional relation
   reification (aka axiom of unique choice, or, principle of (parametric)
   definite descriptions) *)

(** This shows that the axiom of choice can be assumed (under its
   relational formulation) without known inconsistency with classical logic,
   though functional relation reification conflicts with classical logic *)

Lemma description_rel_choice_imp_funct_choice :
  forall A B : Type,
    FunctionalRelReification_on A B -> RelationalChoice_on A B -> FunctionalChoice_on A B.
Proof.
  intros A B Descr RelCh R H.
  destruct (RelCh R H) as (R',(HR'R,H0)).
  destruct (Descr R') as (f,Hf).
  firstorder.
  exists f; intro x.
  destruct (H0 x) as (y,(HR'xy,Huniq)).
  rewrite <- (Huniq (f x) (Hf x)).
  apply HR'R; assumption.
Qed.

Lemma funct_choice_imp_rel_choice :
  forall A B : Type, FunctionalChoice_on A B -> RelationalChoice_on A B.
Proof.
  intros A B FunCh R H.
  destruct (FunCh R H) as (f,H0).
  exists (fun x y => f x = y).
  split.
  intros x y Heq; rewrite <- Heq; trivial.
  intro x; exists (f x); split.
    reflexivity.
    trivial.
Qed.

Lemma funct_choice_imp_description :
  forall A B : Type, FunctionalChoice_on A B -> FunctionalRelReification_on A B.
Proof.
  intros A B FunCh R H.
  destruct (FunCh R) as [f H0].
  (* 1 *)
  intro x.
  destruct (H x) as (y,(HRxy,_)).
  exists y; exact HRxy.
  (* 2 *)
  exists f; exact H0.
Qed.

Corollary FunChoice_Equiv_RelChoice_and_ParamDefinDescr :
  forall A B : Type, FunctionalChoice_on A B <->
    RelationalChoice_on A B /\ FunctionalRelReification_on A B.
Proof.
  intros A B. split.
  intro H; split;
    [ exact (funct_choice_imp_rel_choice H)
      | exact (funct_choice_imp_description H) ].
  intros [H H0]; exact (description_rel_choice_imp_funct_choice H0 H).
Qed.

(**********************************************************************)
(** * Connection between the guarded, non guarded and omniscient choices *)

(** We show that the guarded formulations of the axiom of choice
   are equivalent to their "omniscient" variant and comes from the non guarded
   formulation in presence either of the independence of general premises
   or subset types (themselves derivable from subtypes thanks to proof-
   irrelevance) *)

(**********************************************************************)
(** ** AC_rel + PI -> GAC_rel and AC_rel + IGP -> GAC_rel and GAC_rel = OAC_rel *)

Lemma rel_choice_and_proof_irrel_imp_guarded_rel_choice :
  RelationalChoice -> ProofIrrelevance -> GuardedRelationalChoice.
Proof.
  intros rel_choice proof_irrel.
  red; intros A B P R H.
  destruct (rel_choice _ _ (fun (x:sigT P) (y:B) => R (projT1 x) y)) as (R',(HR'R,H0)).
  intros (x,HPx).
  destruct (H x HPx) as (y,HRxy).
  exists y; exact HRxy.
  set (R'' := fun (x:A) (y:B) => exists H : P x, R' (existT P x H) y).
  exists R''; split.
  intros x y (HPx,HR'xy).
    change x with (projT1 (existT P x HPx)); apply HR'R; exact HR'xy.
  intros x HPx.
  destruct (H0 (existT P x HPx)) as (y,(HR'xy,Huniq)).
  exists y; split. exists HPx; exact HR'xy.
  intros y' (H'Px,HR'xy').
    apply Huniq.
    rewrite proof_irrel with (a1 := HPx) (a2 := H'Px); exact HR'xy'.
Qed.

Lemma rel_choice_indep_of_general_premises_imp_guarded_rel_choice :
  forall A B : Type, inhabited B -> RelationalChoice_on A B ->
    IndependenceOfGeneralPremises -> GuardedRelationalChoice_on A B.
Proof.
  intros A B Inh AC_rel IndPrem P R H.
  destruct (AC_rel (fun x y => P x -> R x y)) as (R',(HR'R,H0)).
  intro x. apply IndPrem. exact Inh. intro Hx.
  apply H; assumption.
  exists (fun x y => P x /\ R' x y).
  firstorder.
Qed.

Lemma guarded_rel_choice_imp_rel_choice :
  forall A B : Type, GuardedRelationalChoice_on A B -> RelationalChoice_on A B.
Proof.
  intros A B GAC_rel R H.
  destruct (GAC_rel (fun _ => True) R) as (R',(HR'R,H0)).
  firstorder.
  exists R'; firstorder.
Qed.

Lemma subset_types_imp_guarded_rel_choice_iff_rel_choice :
  ProofIrrelevance -> (GuardedRelationalChoice <-> RelationalChoice).
Proof.
  intuition auto using
    guarded_rel_choice_imp_rel_choice,
    rel_choice_and_proof_irrel_imp_guarded_rel_choice.
Qed.

(** OAC_rel = GAC_rel *)

Corollary guarded_iff_omniscient_rel_choice :
  GuardedRelationalChoice <-> OmniscientRelationalChoice.
Proof.
  split.
  intros GAC_rel A B R.
  apply (GAC_rel A B (fun x => exists y, R x y) R); auto.
  intros OAC_rel A B P R H.
  destruct (OAC_rel A B R) as (f,Hf); exists f; firstorder.
Qed.

(**********************************************************************)
(** ** AC_fun + IGP = GAC_fun = OAC_fun = AC_fun + Drinker *)

(** AC_fun + IGP = GAC_fun *)

Lemma guarded_fun_choice_imp_indep_of_general_premises :
  GuardedFunctionalChoice -> IndependenceOfGeneralPremises.
Proof.
  intros GAC_fun A P Q Inh H.
  destruct (GAC_fun unit A (fun _ => Q) (fun _ => P) Inh) as (f,Hf).
  tauto.
  exists (f tt); auto.
Qed.


Lemma guarded_fun_choice_imp_fun_choice :
  GuardedFunctionalChoice -> FunctionalChoiceOnInhabitedSet.
Proof.
  intros GAC_fun A B Inh R H.
  destruct (GAC_fun A B (fun _ => True) R Inh) as (f,Hf).
  firstorder.
  exists f; auto.
Qed.

Lemma fun_choice_and_indep_general_prem_imp_guarded_fun_choice :
  FunctionalChoiceOnInhabitedSet -> IndependenceOfGeneralPremises
  -> GuardedFunctionalChoice.
Proof.
  intros AC_fun IndPrem A B P R Inh H.
  apply (AC_fun A B Inh (fun x y => P x -> R x y)).
  intro x; apply IndPrem; eauto.
Qed.

Corollary fun_choice_and_indep_general_prem_iff_guarded_fun_choice :
  FunctionalChoiceOnInhabitedSet /\ IndependenceOfGeneralPremises
  <-> GuardedFunctionalChoice.
Proof.
  intuition auto using
    guarded_fun_choice_imp_indep_of_general_premises,
    guarded_fun_choice_imp_fun_choice,
    fun_choice_and_indep_general_prem_imp_guarded_fun_choice.
Qed.

(** AC_fun + Drinker = OAC_fun *)

(** This was already observed by Bell [[Bell]] *)

Lemma omniscient_fun_choice_imp_small_drinker :
  OmniscientFunctionalChoice -> SmallDrinker'sParadox.
Proof.
  intros OAC_fun A P Inh.
  destruct (OAC_fun unit A (fun _ => P)) as (f,Hf).
  auto.
  exists (f tt); firstorder.
Qed.

Lemma omniscient_fun_choice_imp_fun_choice :
  OmniscientFunctionalChoice -> FunctionalChoiceOnInhabitedSet.
Proof.
  intros OAC_fun A B Inh R H.
  destruct (OAC_fun A B R Inh) as (f,Hf).
  exists f; firstorder.
Qed.

Lemma fun_choice_and_small_drinker_imp_omniscient_fun_choice :
  FunctionalChoiceOnInhabitedSet -> SmallDrinker'sParadox
  -> OmniscientFunctionalChoice.
Proof.
  intros AC_fun Drinker A B R Inh.
  destruct (AC_fun A B Inh (fun x y => (exists y, R x y) -> R x y)) as (f,Hf).
  intro x; apply (Drinker B (R x) Inh).
  exists f; assumption.
Qed.

Corollary fun_choice_and_small_drinker_iff_omniscient_fun_choice :
  FunctionalChoiceOnInhabitedSet /\ SmallDrinker'sParadox
  <-> OmniscientFunctionalChoice.
Proof.
  intuition auto using
    omniscient_fun_choice_imp_small_drinker,
    omniscient_fun_choice_imp_fun_choice,
    fun_choice_and_small_drinker_imp_omniscient_fun_choice.
Qed.

(** OAC_fun = GAC_fun *)

(** This is derivable from the intuitionistic equivalence between IGP and Drinker
but we give a direct proof *)

Theorem guarded_iff_omniscient_fun_choice :
  GuardedFunctionalChoice <-> OmniscientFunctionalChoice.
Proof.
  split.
  intros GAC_fun A B R Inh.
  apply (GAC_fun A B (fun x => exists y, R x y) R); auto.
  intros OAC_fun A B P R Inh H.
  destruct (OAC_fun A B R Inh) as (f,Hf).
  exists f; firstorder.
Qed.

(**********************************************************************)
(** ** D_iota -> ID_iota  and  D_epsilon <-> ID_epsilon + Drinker *)

(** D_iota -> ID_iota *)

Lemma iota_imp_constructive_definite_description :
  IotaStatement -> ConstructiveDefiniteDescription.
Proof.
  intros D_iota A P H.
  destruct D_iota with (P:=P) as (x,H1).
  destruct H; red in H; auto.
  exists x; apply H1; assumption.
Qed.

(** ID_epsilon + Drinker <-> D_epsilon *)

Lemma epsilon_imp_constructive_indefinite_description:
  EpsilonStatement -> ConstructiveIndefiniteDescription.
Proof.
  intros D_epsilon A P H.
  destruct D_epsilon with (P:=P) as (x,H1).
  destruct H; auto.
  exists x; apply H1; assumption.
Qed.

Lemma constructive_indefinite_description_and_small_drinker_imp_epsilon :
  SmallDrinker'sParadox -> ConstructiveIndefiniteDescription ->
  EpsilonStatement.
Proof.
  intros Drinkers D_epsilon A P Inh;
  apply D_epsilon; apply Drinkers; assumption.
Qed.

Lemma epsilon_imp_small_drinker :
  EpsilonStatement -> SmallDrinker'sParadox.
Proof.
  intros D_epsilon A P Inh; edestruct D_epsilon; eauto.
Qed.

Theorem constructive_indefinite_description_and_small_drinker_iff_epsilon :
  (SmallDrinker'sParadox * ConstructiveIndefiniteDescription ->
  EpsilonStatement) *
  (EpsilonStatement ->
   SmallDrinker'sParadox * ConstructiveIndefiniteDescription).
Proof.
  intuition auto using
    epsilon_imp_constructive_indefinite_description,
    constructive_indefinite_description_and_small_drinker_imp_epsilon,
    epsilon_imp_small_drinker.
Qed.

(**********************************************************************)
(** * Derivability of choice for decidable relations with well-ordered codomain *)

(** Countable codomains, such as [nat], can be equipped with a
    well-order, which implies the existence of a least element on
    inhabited decidable subsets. As a consequence, the relational form of
    the axiom of choice is derivable on [nat] for decidable relations.

    We show instead that functional relation reification and the
    functional form of the axiom of choice are equivalent on decidable
    relation with [nat] as codomain
*)

Require Import Wf_nat.
Require Import Decidable.

Definition FunctionalChoice_on_rel (A B:Type) (R:A->B->Prop) :=
  (forall x:A, exists y : B, R x y) ->
  exists f : A -> B, (forall x:A, R x (f x)).

Lemma classical_denumerable_description_imp_fun_choice :
  forall A:Type,
    FunctionalRelReification_on A nat ->
    forall R:A->nat->Prop,
      (forall x y, decidable (R x y)) -> FunctionalChoice_on_rel R.
Proof.
  intros A Descr.
  red; intros R Rdec H.
  set (R':= fun x y => R x y /\ forall y', R x y' -> y <= y').
  destruct (Descr R') as (f,Hf).
  intro x.
  apply (dec_inh_nat_subset_has_unique_least_element (R x)).
    apply Rdec.
    apply (H x).
    exists f.
    intros x.
    destruct (Hf x) as (Hfx,_).
    assumption.
Qed.

(**********************************************************************)
(** * Choice on dependent and non dependent function types are equivalent *)

(** ** Choice on dependent and non dependent function types are equivalent *)

Definition DependentFunctionalChoice_on (A:Type) (B:A -> Type) :=
  forall R:forall x:A, B x -> Prop,
    (forall x:A, exists y : B x, R x y) ->
    (exists f : (forall x:A, B x), forall x:A, R x (f x)).

Notation DependentFunctionalChoice :=
  (forall A (B:A->Type), DependentFunctionalChoice_on B).

(** The easy part *)

Theorem dep_non_dep_functional_choice :
  DependentFunctionalChoice -> FunctionalChoice.
Proof.
  intros AC_depfun A B R H.
  destruct (AC_depfun A (fun _ => B) R H) as (f,Hf).
  exists f; trivial.
Qed.

(** Deriving choice on product types requires some computation on
    singleton propositional types, so we need computational
    conjunction projections and dependent elimination of conjunction
    and equality *)

Scheme and_indd := Induction for and Sort Prop.
Scheme eq_indd := Induction for eq Sort Prop.

Definition proj1_inf (A B:Prop) (p : A/\B) :=
  let (a,b) := p in a.

Theorem non_dep_dep_functional_choice :
  FunctionalChoice -> DependentFunctionalChoice.
Proof.
  intros AC_fun A B R H.
  pose (B' := { x:A & B x }).
  pose (R' := fun (x:A) (y:B') => projT1 y = x /\ R (projT1 y) (projT2 y)).
  destruct (AC_fun A B' R') as (f,Hf).
  intros x. destruct (H x) as (y,Hy).
  exists (existT (fun x => B x) x y). split; trivial.
  exists (fun x => eq_rect _ _ (projT2 (f x)) _ (proj1_inf (Hf x))).
  intro x; destruct (Hf x) as (Heq,HR) using and_indd.
  destruct (f x); simpl in *.
  destruct Heq using eq_indd; trivial.
Qed.

(** ** Reification of dependent and non dependent functional relation  are equivalent *)

Definition DependentFunctionalRelReification_on (A:Type) (B:A -> Type) :=
  forall (R:forall x:A, B x -> Prop),
    (forall x:A, exists! y : B x, R x y) ->
    (exists f : (forall x:A, B x), forall x:A, R x (f x)).

Notation DependentFunctionalRelReification :=
  (forall A (B:A->Type), DependentFunctionalRelReification_on B).

(** The easy part *)

Theorem dep_non_dep_functional_rel_reification :
  DependentFunctionalRelReification -> FunctionalRelReification.
Proof.
  intros DepFunReify A B R H.
  destruct (DepFunReify A (fun _ => B) R H) as (f,Hf).
  exists f; trivial.
Qed.

(** Deriving choice on product types requires some computation on
    singleton propositional types, so we need computational
    conjunction projections and dependent elimination of conjunction
    and equality *)

Theorem non_dep_dep_functional_rel_reification :
  FunctionalRelReification -> DependentFunctionalRelReification.
Proof.
  intros AC_fun A B R H.
  pose (B' := { x:A & B x }).
  pose (R' := fun (x:A) (y:B') => projT1 y = x /\ R (projT1 y) (projT2 y)).
  destruct (AC_fun A B' R') as (f,Hf).
  intros x. destruct (H x) as (y,(Hy,Huni)).
  exists (existT (fun x => B x) x y). repeat split; trivial.
  intros (x',y') (Heqx',Hy').
  simpl in *.
  destruct Heqx'.
  rewrite (Huni y'); trivial.
  exists (fun x => eq_rect _ _ (projT2 (f x)) _ (proj1_inf (Hf x))).
  intro x; destruct (Hf x) as (Heq,HR) using and_indd.
  destruct (f x); simpl in *.
  destruct Heq using eq_indd; trivial.
Qed.

Corollary dep_iff_non_dep_functional_rel_reification :
  FunctionalRelReification <-> DependentFunctionalRelReification.
Proof.
  intuition auto using
    non_dep_dep_functional_rel_reification,
    dep_non_dep_functional_rel_reification.
Qed.

(**********************************************************************)
(** * Non contradiction of constructive descriptions wrt functional axioms of choice *)

(** ** Non contradiction of indefinite description *)

Lemma relative_non_contradiction_of_indefinite_descr :
  forall C:Prop, (ConstructiveIndefiniteDescription -> C)
  -> (FunctionalChoice -> C).
Proof.
  intros C H AC_fun.
  assert (AC_depfun := non_dep_dep_functional_choice AC_fun).
  pose (A0 := { A:Type & { P:A->Prop & exists x, P x }}).
  pose (B0 := fun x:A0 => projT1 x).
  pose (R0 := fun x:A0 => fun y:B0 x => projT1 (projT2 x) y).
  pose (H0 := fun x:A0 => projT2 (projT2 x)).
  destruct (AC_depfun A0 B0 R0 H0) as (f, Hf).
  apply H.
  intros A P H'.
  exists (f (existT _ A (existT _ P H'))).
  pose (Hf' := Hf (existT _ A (existT _ P H'))).
  assumption.
Qed.

Lemma constructive_indefinite_descr_fun_choice :
  ConstructiveIndefiniteDescription -> FunctionalChoice.
Proof.
  intros IndefDescr A B R H.
  exists (fun x => proj1_sig (IndefDescr B (R x) (H x))).
  intro x.
  apply (proj2_sig (IndefDescr B (R x) (H x))).
Qed.

(** ** Non contradiction of definite description *)

Lemma relative_non_contradiction_of_definite_descr :
  forall C:Prop, (ConstructiveDefiniteDescription -> C)
  -> (FunctionalRelReification -> C).
Proof.
  intros C H FunReify.
  assert (DepFunReify := non_dep_dep_functional_rel_reification FunReify).
  pose (A0 := { A:Type & { P:A->Prop & exists! x, P x }}).
  pose (B0 := fun x:A0 => projT1 x).
  pose (R0 := fun x:A0 => fun y:B0 x => projT1 (projT2 x) y).
  pose (H0 := fun x:A0 => projT2 (projT2 x)).
  destruct (DepFunReify A0 B0 R0 H0) as (f, Hf).
  apply H.
  intros A P H'.
  exists (f (existT _ A (existT _ P H'))).
  pose (Hf' := Hf (existT _ A (existT _ P H'))).
  assumption.
Qed.

Lemma constructive_definite_descr_fun_reification :
  ConstructiveDefiniteDescription -> FunctionalRelReification.
Proof.
  intros DefDescr A B R H.
  exists (fun x => proj1_sig (DefDescr B (R x) (H x))).
  intro x.
  apply (proj2_sig (DefDescr B (R x) (H x))).
Qed.

(** Remark, the following corollaries morally hold:

Definition In_propositional_context (A:Type) := forall C:Prop, (A -> C) -> C.

Corollary constructive_definite_descr_in_prop_context_iff_fun_reification :
   In_propositional_context ConstructiveIndefiniteDescription
   <-> FunctionalChoice.

Corollary constructive_definite_descr_in_prop_context_iff_fun_reification :
   In_propositional_context ConstructiveDefiniteDescription
   <-> FunctionalRelReification.

but expecting [FunctionalChoice] (resp. [FunctionalRelReification]) to
be applied on the same Type universes on both sides of the first
(resp. second) equivalence breaks the stratification of universes.
*)

(**********************************************************************)
(** * Excluded-middle + definite description => computational excluded-middle *)

(** The idea for the following proof comes from [[ChicliPottierSimpson02]] *)

(** Classical logic and axiom of unique choice (i.e. functional
    relation reification), as shown in [[ChicliPottierSimpson02]],
    implies the double-negation of excluded-middle in [Set] (which is
    incompatible with the impredicativity of [Set]).

    We adapt the proof to show that constructive definite description
    transports excluded-middle from [Prop] to [Set].

    [[ChicliPottierSimpson02]] Laurent Chicli, Loïc Pottier, Carlos
    Simpson, Mathematical Quotients and Quotient Types in Coq,
    Proceedings of TYPES 2002, Lecture Notes in Computer Science 2646,
    Springer Verlag.  *)

Require Import Setoid.

Theorem constructive_definite_descr_excluded_middle :
  (forall A : Type, ConstructiveDefiniteDescription_on A) ->
  (forall P:Prop, P \/ ~ P) -> (forall P:Prop, {P} + {~ P}).
Proof.
  intros Descr EM P.
  pose (select := fun b:bool => if b then P else ~P).
  assert { b:bool | select b } as ([|],HP).
  red in Descr.
  apply Descr.
  rewrite <- unique_existence; split.
  destruct (EM P).
  exists true; trivial.
  exists false; trivial.
  intros [|] [|] H1 H2; simpl in *; reflexivity || contradiction.
  left; trivial.
  right; trivial.
Qed.

Corollary fun_reification_descr_computational_excluded_middle_in_prop_context :
  FunctionalRelReification ->
  (forall P:Prop, P \/ ~ P) ->
  forall C:Prop, ((forall P:Prop, {P} + {~ P}) -> C) -> C.
Proof.
  intros FunReify EM C H. intuition auto using
    constructive_definite_descr_excluded_middle,
    (relative_non_contradiction_of_definite_descr (C:=C)).
Qed.

(**********************************************************************)
(** * Choice => Dependent choice => Countable choice *)
(* The implications below are standard *)

Require Import Arith.

Theorem functional_choice_imp_functional_dependent_choice :
   FunctionalChoice -> FunctionalDependentChoice.
Proof.
  intros FunChoice A R HRfun x0.
  apply FunChoice in HRfun as (g,Rg).
  set (f:=fix f n := match n with 0 => x0 | S n' => g (f n') end).
  exists f; firstorder.
Qed.

Theorem functional_dependent_choice_imp_functional_countable_choice :
   FunctionalDependentChoice -> FunctionalCountableChoice.
Proof.
  intros H A R H0.
  set (R' (p q:nat*A) := fst q = S (fst p) /\ R (fst p) (snd q)).
  destruct (H0 0) as (y0,Hy0).
  destruct H with (R:=R') (x0:=(0,y0)) as (f,(Hf0,HfS)).
    intro x; destruct (H0 (fst x)) as (y,Hy).
    exists (S (fst x),y).
    red. auto.
  assert (Heq:forall n, fst (f n) = n).
    induction n.
      rewrite Hf0; reflexivity.
      specialize HfS with n; destruct HfS as (->,_); congruence.
  exists (fun n => snd (f (S n))).
  intro n'. specialize HfS with n'.
  destruct HfS as (_,HR).
  rewrite Heq in HR.
  assumption.
Qed.

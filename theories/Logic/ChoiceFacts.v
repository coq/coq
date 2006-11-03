(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Some facts and definitions concerning choice and description in
       intuitionistic logic.

We investigate the relations between the following choice and
description principles

- AC_rel  = relational form of the (non extensional) axiom of choice
            (a "set-theoretic" axiom of choice)
- AC_fun  = functional form of the (non extensional) axiom of choice
            (a "type-theoretic" axiom of choice)
- AC!     = functional relation reification
            (known as axiom of unique choice in topos theory,
             sometimes called principle of definite description in 
             the context of constructive type theory)

- GAC_rel = guarded relational form of the (non extensional) axiom of choice
- GAC_fun = guarded functional form of the (non extensional) axiom of choice
- GAC!    = guarded functional relation reification

- OAC_rel = "omniscient" relational form of the (non extensional) axiom of choice
- OAC_fun = "omniscient" functional form of the (non extensional) axiom of choice
            (called AC* in Bell [Bell])
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
            (called Ex in Bell [Bell])  

We let also

IPL_2^2 = 2nd-order impredicative, 2nd-order functional minimal predicate logic
IPL_2   = 2nd-order impredicative minimal predicate logic
IPL^2   = 2nd-order functional minimal predicate logic (with ex. quant.)

Table of contents

1. Definitions

2. IPL_2^2 |- AC_rel + AC! = AC_fun

3. 1. AC_rel + PI -> GAC_rel  and  PL_2 |- AC_rel + IGP -> GAC_rel and GAC_rel = OAC_rel

4. 2. IPL^2 |- AC_fun + IGP = GAC_fun = OAC_fun = AC_fun + Drinker

5. Derivability of choice for decidable relations with well-ordered codomain

6. Equivalence of choices on dependent or non dependent functional types

7. Non contradiction of constructive descriptions wrt functional choices

8. Definite description transports classical logic to the computational world

References:

[Bell] John L. Bell, Choice principles in intuitionistic set theory,
unpublished.

[Bell93] John L. Bell, Hilbert's Epsilon Operator in Intuitionistic
Type Theories, Mathematical Logic Quarterly, volume 39, 1993.

[Carlstr�m05] Jesper Carlstr�m, Interpreting descriptions in
intentional type theory, Journal of Symbolic Logic 70(2):488-514, 2005.
*)

Set Implicit Arguments.

Notation Local "'inhabited' A" := A (at level 10, only parsing).

(**********************************************************************)
(** * Definitions *)

(** Choice, reification and description schemes *)

Section ChoiceSchemes.

Variables A B :Type.

Variables P:A->Prop.

Variables R:A->B->Prop.

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

(** AC! or Functional Relation Reification (known as Axiom of Unique Choice
    in topos theory; also called principle of definite description *)

Definition FunctionalRelReification_on :=
  forall R:A->B->Prop,
    (forall x : A, exists! y : B, R x y) ->
    (exists f : A->B, forall x : A, R x (f x)).

(** ID_epsilon (constructive version of indefinite description;
    combined with proof-irrelevance, it may be connected to
    Carlstr�m's type theory with a constructive indefinite description
    operator) *)

Definition ConstructiveIndefiniteDescription_on :=
  forall P:A->Prop,
    (exists x, P x) -> { x:A | P x }.

(** ID_iota (constructive version of definite description; combined
    with proof-irrelevance, it may be connected to Carlstr�m's and
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

Definition ClassicalIndefiniteDescription := 
  forall P:A->Prop,
    A -> { x:A | (exists x, P x) -> P x }.

(** D_iota *)

Definition ClassicalDefiniteDescription := 
  forall P:A->Prop,
    A -> { x:A | (exists! x, P x) -> P x }.

End ChoiceSchemes.

(** Generalized schemes *)

Notation RelationalChoice :=
  (forall A B, RelationalChoice_on A B).
Notation FunctionalChoice :=
  (forall A B, FunctionalChoice_on A B).
Notation FunctionalChoiceOnInhabitedSet :=
  (forall A B, inhabited B -> FunctionalChoice_on A B).
Notation FunctionalRelReification :=
  (forall A B, FunctionalRelReification_on A B).

Notation GuardedRelationalChoice := 
  (forall A B, GuardedRelationalChoice_on A B).
Notation GuardedFunctionalChoice :=
  (forall A B, GuardedFunctionalChoice_on A B).
Notation GuardedFunctionalRelReification :=
  (forall A B, GuardedFunctionalRelReification_on A B).

Notation OmniscientRelationalChoice :=
  (forall A B, OmniscientRelationalChoice_on A B).
Notation OmniscientFunctionalChoice :=
  (forall A B, OmniscientFunctionalChoice_on A B).

Notation ConstructiveDefiniteDescription := 
  (forall A, ConstructiveDefiniteDescription_on A).
Notation ConstructiveIndefiniteDescription := 
  (forall A, ConstructiveIndefiniteDescription_on A).

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
(** * AC_rel + PDP = AC_fun

   We show that the functional formulation of the axiom of Choice
   (usual formulation in type theory) is equivalent to its relational
   formulation (only formulation of set theory) + the axiom of
   (parametric) definite description (aka axiom of unique choice) *)

(** This shows that the axiom of choice can be assumed (under its
   relational formulation) without known inconsistency with classical logic,
   though definite description conflicts with classical logic *)

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
  forall A B, FunctionalChoice_on A B -> RelationalChoice_on A B.
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
  forall A B, FunctionalChoice_on A B -> FunctionalRelReification_on A B.
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

Theorem FunChoice_Equiv_RelChoice_and_ParamDefinDescr :
  forall A B, FunctionalChoice_on A B <-> 
    RelationalChoice_on A B /\ FunctionalRelReification_on A B.
Proof.
  intros A B; split.
  intro H; split;
    [ exact (funct_choice_imp_rel_choice H)
      | exact (funct_choice_imp_description H) ].
  intros [H H0]; exact (description_rel_choice_imp_funct_choice H0 H).
Qed.

(**********************************************************************)
(** * Connection between the guarded, non guarded and descriptive choices and *)

(** We show that the guarded relational formulation of the axiom of Choice
   comes from the non guarded formulation in presence either of the
   independance of premises or proof-irrelevance *)

(**********************************************************************)
(** ** AC_rel + PI -> GAC_rel and AC_rel + IGP -> GAC_rel and GAC_rel = OAC_rel *)

Lemma rel_choice_and_proof_irrel_imp_guarded_rel_choice :
  RelationalChoice -> ProofIrrelevance -> GuardedRelationalChoice.
Proof.
  intros rel_choice proof_irrel.
  red in |- *; intros A B P R H.
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
  forall A B, inhabited B -> RelationalChoice_on A B -> 
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
  forall A B, GuardedRelationalChoice_on A B -> RelationalChoice_on A B.
Proof.
  intros A B GAC_rel R H.
  destruct (GAC_rel (fun _ => True) R) as (R',(HR'R,H0)).
  firstorder.
  exists R'; firstorder.
Qed.

(** OAC_rel = GAC_rel *)

Lemma guarded_iff_omniscient_rel_choice :
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

(** AC_fun + Drinker = OAC_fun *)

(** This was already observed by Bell [Bell] *)

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

(** OAC_fun = GAC_fun *)

(** This is derivable from the intuitionistic equivalence between IGP and Drinker
but we give a direct proof *)

Lemma guarded_iff_omniscient_fun_choice :
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
Require Import Compare_dec.
Require Import Decidable.
Require Import Arith.

Definition has_unique_least_element (A:Type) (R:A->A->Prop) (P:A->Prop) :=
  exists! x, P x /\ forall x', P x' -> R x x'.

Lemma dec_inh_nat_subset_has_unique_least_element :
  forall P:nat->Prop, (forall n, P n \/ ~ P n) ->
    (exists n, P n) -> has_unique_least_element le P.
Proof.
  intros P Pdec (n0,HPn0).
  assert
    (forall n, (exists n', n'<n /\ P n' /\ forall n'', P n'' -> n'<=n'')
      \/(forall n', P n' -> n<=n')).
  induction n.
  right.
  intros n' Hn'.
  apply le_O_n.
  destruct IHn.
  left; destruct H as (n', (Hlt', HPn')).
  exists n'; split.
  apply lt_S; assumption.
  assumption.
  destruct (Pdec n).
  left; exists n; split.
  apply lt_n_Sn.
  split; assumption.
  right.
  intros n' Hltn'.
  destruct (le_lt_eq_dec n n') as [Hltn|Heqn].
  apply H; assumption.
  assumption.
  destruct H0.
  rewrite Heqn; assumption.
  destruct (H n0) as [(n,(Hltn,(Hmin,Huniqn)))|]; [exists n | exists n0];
    repeat split;
      assumption || intros n' (HPn',Hminn'); apply le_antisym; auto.
Qed.

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
  red in |- *; intros R Rdec H.
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

(**********************************************************************)
(** * Non contradiction of constructive descriptions wrt functional axioms of choice *)

(** ** Non contradiction of indefinite description *)

Lemma relative_non_contradiction_of_indefinite_desc :
  (ConstructiveIndefiniteDescription -> False)
  -> (FunctionalChoice -> False).
Proof.
  intros H AC_fun.
  assert (AC_depfun := non_dep_dep_functional_choice AC_fun).
  pose (A0 := { A:Type & { P:A->Prop & exists x, P x }}).
  pose (B0 := fun x:A0 => projT1 x).
  pose (R0 := fun x:A0 => fun y:B0 x => projT1 (projT2 x) y).
  pose (H0 := fun x:A0 => projT2 (projT2 x)).
  destruct (AC_depfun A0 B0 R0 H0) as (f, Hf).
  apply H.
  intros A P H'.
  exists (f (existT (fun _ => sigT _) A
    (existT (fun P => exists x, P x) P H'))).
  pose (Hf' := 
    Hf (existT (fun _ => sigT _) A
      (existT (fun P => exists x, P x) P H'))).
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
  (ConstructiveDefiniteDescription -> False)
  -> (FunctionalRelReification -> False).
Proof.
  intros H FunReify.
  assert (DepFunReify := non_dep_dep_functional_rel_reification FunReify).
  pose (A0 := { A:Type & { P:A->Prop & exists! x, P x }}).
  pose (B0 := fun x:A0 => projT1 x).
  pose (R0 := fun x:A0 => fun y:B0 x => projT1 (projT2 x) y).
  pose (H0 := fun x:A0 => projT2 (projT2 x)).
  destruct (DepFunReify A0 B0 R0 H0) as (f, Hf).
  apply H.
  intros A P H'.
  exists (f (existT (fun _ => sigT _) A
    (existT (fun P => exists! x, P x) P H'))).
  pose (Hf' := 
    Hf (existT (fun _ => sigT _) A
      (existT (fun P => exists! x, P x) P H'))).
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

(**********************************************************************)
(** * Excluded-middle + definite description => computational excluded-middle *)

(** The idea for the following proof comes from [ChicliPottierSimpson02] *)

(** Classical logic and axiom of unique choice (i.e. functional
    relation reification), as shown in [ChicliPottierSimpson02],
    implies the double-negation of excluded-middle in [Set] (which is
    incompatible with the impredicativity of [Set]).

    We adapt the proof to show that constructive definite description
    transports excluded-middle from [Prop] to [Set].

    [ChicliPottierSimpson02] Laurent Chicli, Lo�c Pottier, Carlos
    Simpson, Mathematical Quotients and Quotient Types in Coq,
    Proceedings of TYPES 2002, Lecture Notes in Computer Science 2646,
    Springer Verlag.  *)

Require Import Setoid.

Theorem constructive_definite_descr_excluded_middle :
  ConstructiveDefiniteDescription ->
  (forall P:Prop, P \/ ~ P) -> (forall P:Prop, {P} + {~ P}).
Proof.
  intros Descr EM P.
  pose (select := fun b:bool => if b then P else ~P).
  assert { b:bool | select b } as ([|],HP).
  apply Descr.
  rewrite <- unique_existence; split.
  destruct (EM P).
  exists true; trivial.
  exists false; trivial.
  intros [|] [|] H1 H2; simpl in *; reflexivity || contradiction.
  left; trivial.
  right; trivial.
Qed.  

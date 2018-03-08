(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(************************************************************************)

(** Some facts and definitions concerning choice and description in
       intuitionistic logic. *)
(** * References: *)
(**
[[Bell]] John L. Bell, Choice principles in intuitionistic set theory,
unpublished.

[[Bell93]] John L. Bell, Hilbert's Epsilon Operator in Intuitionistic
Type Theories, Mathematical Logic Quarterly, volume 39, 1993.

[[Carlström04]] Jesper Carlström, EM + Ext_ + AC_int is equivalent to
AC_ext, Mathematical Logic Quaterly, vol 50(3), pp 236-240, 2004.

[[Carlström05]] Jesper Carlström, Interpreting descriptions in
intentional type theory, Journal of Symbolic Logic 70(2):488-514, 2005.

[[Werner97]] Benjamin Werner, Sets in Types, Types in Sets, TACS, 1997.
*)

Require Import RelationClasses Logic.

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

(** ** Constructive choice and description *)

(** AC_rel = relational form of the (non extensional) axiom of choice
             (a "set-theoretic" axiom of choice) *)

Definition RelationalChoice_on :=
  forall R:A->B->Prop,
    (forall x : A, exists y : B, R x y) ->
    (exists R' : A->B->Prop, subrelation R' R /\ forall x, exists! y, R' x y).

(** AC_fun = functional form of the (non extensional) axiom of choice
             (a "type-theoretic" axiom of choice) *)

(* Note: This is called Type-Theoretic Description Axiom (TTDA) in
   [[Werner97]] (using a non-standard meaning of "description"). This
   is called intensional axiom of choice (AC_int) in [[Carlström04]] *)

Definition FunctionalChoice_on_rel (R:A->B->Prop) :=
  (forall x:A, exists y : B, R x y) ->
  exists f : A -> B, (forall x:A, R x (f x)).

Definition FunctionalChoice_on :=
  forall R:A->B->Prop,
    (forall x : A, exists y : B, R x y) ->
    (exists f : A->B, forall x : A, R x (f x)).

(** AC_fun_dep = functional form of the (non extensional) axiom of
                 choice, with dependent functions *)
Definition DependentFunctionalChoice_on (A:Type) (B:A -> Type) :=
  forall R:forall x:A, B x -> Prop,
    (forall x:A, exists y : B x, R x y) ->
    (exists f : (forall x:A, B x), forall x:A, R x (f x)).

(** AC_trunc = axiom of choice for propositional truncations
               (truncation and quantification commute) *)
Definition InhabitedForallCommute_on (A : Type) (B : A -> Type) :=
  (forall x, inhabited (B x)) -> inhabited (forall x, B x).

(** DC_fun = functional form of the dependent axiom of choice *)

Definition FunctionalDependentChoice_on :=
  forall (R:A->A->Prop),
    (forall x, exists y, R x y) -> forall x0,
    (exists f : nat -> A, f 0 = x0 /\ forall n, R (f n) (f (S n))).

(** ACw_fun = functional form of the countable axiom of choice *)

Definition FunctionalCountableChoice_on :=
  forall (R:nat->A->Prop),
    (forall n, exists y, R n y) ->
    (exists f : nat -> A, forall n, R n (f n)).

(** AC! = functional relation reification
          (known as axiom of unique choice in topos theory,
           sometimes called principle of definite description in
           the context of constructive type theory, sometimes
           called axiom of no choice) *)

Definition FunctionalRelReification_on :=
  forall R:A->B->Prop,
    (forall x : A, exists! y : B, R x y) ->
    (exists f : A->B, forall x : A, R x (f x)).

(** AC_dep! = functional relation reification, with dependent functions
              see AC! *)
Definition DependentFunctionalRelReification_on (A:Type) (B:A -> Type) :=
  forall (R:forall x:A, B x -> Prop),
    (forall x:A, exists! y : B x, R x y) ->
    (exists f : (forall x:A, B x), forall x:A, R x (f x)).

(** AC_fun_repr = functional choice of a representative in an equivalence class *)

(* Note: This is called Type-Theoretic Choice Axiom (TTCA) in
   [[Werner97]] (by reference to the extensional set-theoretic
   formulation of choice); Note also a typo in its intended
   formulation in [[Werner97]]. *)

Definition RepresentativeFunctionalChoice_on :=
  forall R:A->A->Prop,
    (Equivalence R) ->
    (exists f : A->A, forall x : A, (R x (f x)) /\ forall x', R x x' -> f x = f x').

(** AC_fun_setoid = functional form of the (so-called extensional) axiom of
                    choice from setoids *)

Definition SetoidFunctionalChoice_on :=
  forall R : A -> A -> Prop,
  forall T : A -> B -> Prop,
  Equivalence R ->
  (forall x x' y, R x x' -> T x y -> T x' y) ->
  (forall x, exists y, T x y) ->
  exists f : A -> B, forall x : A, T x (f x) /\ (forall x' : A, R x x' -> f x = f x').

(** AC_fun_setoid_gen = functional form of the general form of the (so-called
                        extensional) axiom of choice over setoids *)

(* Note: This is called extensional axiom of choice (AC_ext) in
   [[Carlström04]]. *)

Definition GeneralizedSetoidFunctionalChoice_on :=
  forall R : A -> A -> Prop,
  forall S : B -> B -> Prop,
  forall T : A -> B -> Prop,
  Equivalence R ->
  Equivalence S ->
  (forall x x' y y', R x x' -> S y y' -> T x y -> T x' y') ->
  (forall x, exists y, T x y) ->
  exists f : A -> B,
    forall x : A, T x (f x) /\ (forall x' : A, R x x' -> S (f x) (f x')).

(** AC_fun_setoid_simple = functional form of the (so-called extensional) axiom of
                           choice from setoids on locally compatible relations *)

Definition SimpleSetoidFunctionalChoice_on A B :=
  forall R : A -> A -> Prop,
  forall T : A -> B -> Prop,
  Equivalence R ->
  (forall x, exists y, forall x', R x x' -> T x' y) ->
  exists f : A -> B, forall x : A, T x (f x) /\ (forall x' : A, R x x' -> f x = f x').

(** ID_epsilon = constructive version of indefinite description;
                 combined with proof-irrelevance, it may be connected to
                 Carlström's type theory with a constructive indefinite description
                 operator *)

Definition ConstructiveIndefiniteDescription_on :=
  forall P:A->Prop,
    (exists x, P x) -> { x:A | P x }.

(** ID_iota = constructive version of definite description;
              combined with proof-irrelevance, it may be connected to
              Carlström's and Stenlund's type theory with a
              constructive definite description operator) *)

Definition ConstructiveDefiniteDescription_on :=
  forall P:A->Prop,
    (exists! x, P x) -> { x:A | P x }.

(** ** Weakly classical choice and description *)

(** GAC_rel = guarded relational form of the (non extensional) axiom of choice *)

Definition GuardedRelationalChoice_on :=
  forall P : A->Prop, forall R : A->B->Prop,
    (forall x : A, P x -> exists y : B, R x y) ->
    (exists R' : A->B->Prop,
      subrelation R' R /\ forall x, P x -> exists! y, R' x y).

(** GAC_fun = guarded functional form of the (non extensional) axiom of choice *)

Definition GuardedFunctionalChoice_on :=
  forall P : A->Prop, forall R : A->B->Prop,
    inhabited B ->
    (forall x : A, P x -> exists y : B, R x y) ->
    (exists f : A->B, forall x, P x -> R x (f x)).

(** GAC! = guarded functional relation reification *)

Definition GuardedFunctionalRelReification_on :=
  forall P : A->Prop, forall R : A->B->Prop,
    inhabited B ->
    (forall x : A, P x -> exists! y : B, R x y) ->
    (exists f : A->B, forall x : A, P x -> R x (f x)).

(** OAC_rel = "omniscient" relational form of the (non extensional) axiom of choice *)

Definition OmniscientRelationalChoice_on :=
  forall R : A->B->Prop,
    exists R' : A->B->Prop,
      subrelation R' R /\ forall x : A, (exists y : B, R x y) -> exists! y, R' x y.

(** OAC_fun = "omniscient" functional form of the (non extensional) axiom of choice
              (called AC* in Bell [[Bell]]) *)

Definition OmniscientFunctionalChoice_on :=
  forall R : A->B->Prop,
    inhabited B ->
    exists f : A->B, forall x : A, (exists y : B, R x y) -> R x (f x).

(** D_epsilon = (weakly classical) indefinite description principle *)

Definition EpsilonStatement_on :=
  forall P:A->Prop,
    inhabited A -> { x:A | (exists x, P x) -> P x }.

(** D_iota = (weakly classical) definite description principle *)

Definition IotaStatement_on :=
  forall P:A->Prop,
    inhabited A -> { x:A | (exists! x, P x) -> P x }.

End ChoiceSchemes.

(** Generalized schemes *)

Notation RelationalChoice :=
  (forall A B : Type, RelationalChoice_on A B).
Notation FunctionalChoice :=
  (forall A B : Type, FunctionalChoice_on A B).
Notation DependentFunctionalChoice :=
  (forall A (B:A->Type), DependentFunctionalChoice_on B).
Notation InhabitedForallCommute :=
  (forall A (B : A -> Type), InhabitedForallCommute_on B).
Notation FunctionalDependentChoice :=
  (forall A : Type, FunctionalDependentChoice_on A).
Notation FunctionalCountableChoice :=
  (forall A : Type, FunctionalCountableChoice_on A).
Notation FunctionalChoiceOnInhabitedSet :=
  (forall A B : Type, inhabited B -> FunctionalChoice_on A B).
Notation FunctionalRelReification :=
  (forall A B : Type, FunctionalRelReification_on A B).
Notation DependentFunctionalRelReification :=
  (forall A (B:A->Type), DependentFunctionalRelReification_on B).
Notation RepresentativeFunctionalChoice :=
  (forall A : Type, RepresentativeFunctionalChoice_on A).
Notation SetoidFunctionalChoice :=
  (forall A  B: Type, SetoidFunctionalChoice_on A B).
Notation GeneralizedSetoidFunctionalChoice :=
  (forall A B : Type, GeneralizedSetoidFunctionalChoice_on A B).
Notation SimpleSetoidFunctionalChoice :=
  (forall A B : Type, SimpleSetoidFunctionalChoice_on A B).

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

(** PI = proof irrelevance *)
Definition ProofIrrelevance :=
  forall (A:Prop) (a1 a2:A), a1 = a2.

(** IGP = independence of general premises
          (an unconstrained generalisation of the constructive principle of
           independence of premises) *)
Definition IndependenceOfGeneralPremises :=
  forall (A:Type) (P:A -> Prop) (Q:Prop),
    inhabited A ->
    (Q -> exists x, P x) -> exists x, Q -> P x.

(** Drinker = drinker's paradox (small form)
              (called Ex in Bell [[Bell]]) *)
Definition SmallDrinker'sParadox :=
  forall (A:Type) (P:A -> Prop), inhabited A ->
    exists x, (exists x, P x) -> P x.

(** EM = excluded-middle *)
Definition ExcludedMiddle :=
  forall P:Prop, P \/ ~ P.

(** Extensional schemes *)

(** Ext_prop_repr = choice of a representative among extensional propositions *)
Local Notation ExtensionalPropositionRepresentative :=
  (forall (A:Type),
   exists h : Prop -> Prop,
   forall P : Prop, (P <-> h P) /\ forall Q, (P <-> Q) -> h P = h Q).

(** Ext_pred_repr = choice of a representative among extensional predicates *)
Local Notation ExtensionalPredicateRepresentative :=
  (forall (A:Type),
   exists h : (A->Prop) -> (A->Prop),
   forall (P : A -> Prop), (forall x, P x <-> h P x) /\ forall Q, (forall x, P x <-> Q x) -> h P = h Q).

(** Ext_fun_repr = choice of a representative among extensional functions *)
Local Notation ExtensionalFunctionRepresentative :=
  (forall (A B:Type),
   exists h : (A->B) -> (A->B),
   forall (f : A -> B), (forall x, f x = h f x) /\ forall g, (forall x, f x = g x) -> h f = h g).

(** We let also

- IPL_2   = 2nd-order impredicative minimal predicate logic (with ex. quant.)
- IPL^2   = 2nd-order functional minimal predicate logic (with ex. quant.)
- IPL_2^2 = 2nd-order impredicative, 2nd-order functional minimal pred. logic (with ex. quant.)

with no prerequisite on the non-emptiness of domains
*)

(**********************************************************************)
(** * Table of contents *)

(* This is very fragile. *)
(**
1. Definitions

2. IPL_2^2 |- AC_rel + AC! = AC_fun

3.1. typed IPL_2 + Sigma-types + PI |- AC_rel = GAC_rel  and  IPL_2 |- AC_rel + IGP -> GAC_rel and IPL_2 |- GAC_rel = OAC_rel

3.2. IPL^2 |- AC_fun + IGP = GAC_fun = OAC_fun = AC_fun + Drinker

3.3. D_iota -> ID_iota  and  D_epsilon <-> ID_epsilon + Drinker

4. Derivability of choice for decidable relations with well-ordered codomain

5. AC_fun = AC_fun_dep = AC_trunc

6. Non contradiction of constructive descriptions wrt functional choices

7. Definite description transports classical logic to the computational world

8. Choice -> Dependent choice -> Countable choice

9.1. AC_fun_setoid = AC_fun + Ext_fun_repr + EM

9.2. AC_fun_setoid = AC_fun + Ext_pred_repr + PI
 *)

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

Lemma functional_rel_reification_and_rel_choice_imp_fun_choice :
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

Lemma fun_choice_imp_rel_choice :
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

Lemma fun_choice_imp_functional_rel_reification :
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

Corollary fun_choice_iff_rel_choice_and_functional_rel_reification :
  forall A B : Type, FunctionalChoice_on A B <->
    RelationalChoice_on A B /\ FunctionalRelReification_on A B.
Proof.
  intros A B. split.
  intro H; split;
    [ exact (fun_choice_imp_rel_choice H)
      | exact (fun_choice_imp_functional_rel_reification H) ].
  intros [H H0]; exact (functional_rel_reification_and_rel_choice_imp_fun_choice H0 H).
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
(** * AC_fun = AC_fun_dep = AC_trunc *)

(** ** Choice on dependent and non dependent function types are equivalent *)

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

(** ** Functional choice and truncation choice are equivalent *)

Theorem functional_choice_to_inhabited_forall_commute :
  FunctionalChoice -> InhabitedForallCommute.
Proof.
  intros choose0 A B Hinhab.
  pose proof (non_dep_dep_functional_choice choose0) as choose;clear choose0.
  assert (Hexists : forall x, exists _ : B x, True).
  { intros x;apply inhabited_sig_to_exists.
    refine (inhabited_covariant _ (Hinhab x)).
    intros y;exists y;exact I. }
  apply choose in Hexists.
  destruct Hexists as [f _].
  exact (inhabits f).
Qed.

Theorem inhabited_forall_commute_to_functional_choice :
  InhabitedForallCommute -> FunctionalChoice.
Proof.
  intros choose A B R Hexists.
  assert (Hinhab : forall x, inhabited {y : B | R x y}).
  { intros x;apply exists_to_inhabited_sig;trivial. }
  apply choose in Hinhab. destruct Hinhab as [f].
  exists (fun x => proj1_sig (f x)).
  exact (fun x => proj2_sig (f x)).
Qed.

(** ** Reification of dependent and non dependent functional relation  are equivalent *)

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

(**********************************************************************)
(** * About the axiom of choice over setoids                          *)

Require Import ClassicalFacts PropExtensionalityFacts.

(**********************************************************************)
(** ** Consequences of the choice of a representative in an equivalence class *)

Theorem repr_fun_choice_imp_ext_prop_repr :
  RepresentativeFunctionalChoice -> ExtensionalPropositionRepresentative.
Proof.
  intros ReprFunChoice A.
  pose (R P Q := P <-> Q).
  assert (Hequiv:Equivalence R) by (split; firstorder).
  apply (ReprFunChoice _ R Hequiv).
Qed.

Theorem repr_fun_choice_imp_ext_pred_repr :
  RepresentativeFunctionalChoice -> ExtensionalPredicateRepresentative.
Proof.
  intros ReprFunChoice A.
  pose (R P Q := forall x : A, P x <-> Q x).
  assert (Hequiv:Equivalence R) by (split; firstorder).
  apply (ReprFunChoice _ R Hequiv).
Qed.

Theorem repr_fun_choice_imp_ext_function_repr :
  RepresentativeFunctionalChoice -> ExtensionalFunctionRepresentative.
Proof.
  intros ReprFunChoice A B.
  pose (R (f g : A -> B) := forall x : A, f x = g x).
  assert (Hequiv:Equivalence R).
  { split; try easy. firstorder using eq_trans. }
  apply (ReprFunChoice _ R Hequiv).
Qed.

(** *** This is a variant of Diaconescu and Goodman-Myhill theorems *)

Theorem repr_fun_choice_imp_excluded_middle :
  RepresentativeFunctionalChoice -> ExcludedMiddle.
Proof.
  intros ReprFunChoice.
  apply representative_boolean_partition_imp_excluded_middle, ReprFunChoice.
Qed.

Theorem repr_fun_choice_imp_relational_choice :
  RepresentativeFunctionalChoice -> RelationalChoice.
Proof.
  intros ReprFunChoice A B T Hexists.
  pose (D := (A*B)%type).
  pose (R (z z':D) :=
    let x := fst z in
    let x' := fst z' in
    let y := snd z in
    let y' := snd z' in
    x = x' /\ (T x y -> y = y' \/ T x y') /\ (T x y' -> y = y' \/ T x y)).
  assert (Hequiv : Equivalence R).
  { split.
    - split. easy. firstorder.
    - intros (x,y) (x',y') (H1,(H2,H2')). split. easy. simpl fst in *. simpl snd in *.
      subst x'. split; intro H.
      + destruct (H2' H); firstorder.
      + destruct (H2 H); firstorder.
    - intros (x,y) (x',y') (x'',y'') (H1,(H2,H2')) (H3,(H4,H4')).
      simpl fst in *. simpl snd in *. subst x'' x'. split. easy. split; intro H.
      + simpl fst in *. simpl snd in *. destruct (H2 H) as [<-|H0].
        * destruct (H4 H); firstorder.
        * destruct (H2' H0), (H4 H0); try subst y'; try subst y''; try firstorder.
      + simpl fst in *. simpl snd in *. destruct (H4' H) as [<-|H0].
        * destruct (H2' H); firstorder.
        * destruct (H2' H0), (H4 H0); try subst y'; try subst y''; try firstorder. }
  destruct (ReprFunChoice D R Hequiv) as (g,Hg).
  set (T' x y := T x y /\ exists y', T x y' /\ g (x,y') = (x,y)).
  exists T'. split.
  - intros x y (H,_); easy.
  - intro x. destruct (Hexists x) as (y,Hy).
    exists (snd (g (x,y))).
    destruct (Hg (x,y)) as ((Heq1,(H',H'')),Hgxyuniq); clear Hg.
    destruct (H' Hy) as [Heq2|Hgy]; clear H'.
    + split. split.
      * rewrite <- Heq2. assumption.
      * exists y. destruct (g (x,y)) as (x',y'). simpl in Heq1, Heq2. subst; easy.
      * intros y' (Hy',(y'',(Hy'',Heq))).
        rewrite (Hgxyuniq (x,y'')), Heq. easy. split. easy.
        split; right; easy.
    + split. split.
      * assumption.
      * exists y. destruct (g (x,y)) as (x',y'). simpl in Heq1. subst x'; easy.
      * intros y' (Hy',(y'',(Hy'',Heq))).
        rewrite (Hgxyuniq (x,y'')), Heq. easy. split. easy.
        split; right; easy.
Qed.

(**********************************************************************)
(** ** AC_fun_setoid = AC_fun_setoid_gen = AC_fun_setoid_simple       *)

Theorem gen_setoid_fun_choice_imp_setoid_fun_choice  :
  forall A B, GeneralizedSetoidFunctionalChoice_on A B -> SetoidFunctionalChoice_on A B.
Proof.
  intros A B GenSetoidFunChoice R T Hequiv Hcompat Hex.
  apply GenSetoidFunChoice; try easy.
  apply eq_equivalence.
  intros * H <-. firstorder.
Qed.

Theorem setoid_fun_choice_imp_gen_setoid_fun_choice :
  forall A B, SetoidFunctionalChoice_on A B -> GeneralizedSetoidFunctionalChoice_on A B.
Proof.
  intros A B SetoidFunChoice R S T HequivR HequivS Hcompat Hex.
  destruct SetoidFunChoice with (R:=R) (T:=T) as (f,Hf); try easy.
  { intros; apply (Hcompat x x' y y); try easy. }
  exists f. intros x; specialize Hf with x as (Hf,Huniq). intuition. now erewrite Huniq.
Qed.

Corollary setoid_fun_choice_iff_gen_setoid_fun_choice :
  forall A B, SetoidFunctionalChoice_on A B <-> GeneralizedSetoidFunctionalChoice_on A B.
Proof.
  split; auto using gen_setoid_fun_choice_imp_setoid_fun_choice, setoid_fun_choice_imp_gen_setoid_fun_choice.
Qed.

Theorem setoid_fun_choice_imp_simple_setoid_fun_choice  :
   forall A B, SetoidFunctionalChoice_on A B -> SimpleSetoidFunctionalChoice_on A B.
Proof.
  intros A B SetoidFunChoice R T Hequiv Hexists.
  pose (T' x y := forall x', R x x' -> T x' y).
  assert (Hcompat : forall (x x' : A) (y : B), R x x' -> T' x y -> T' x' y) by firstorder.
  destruct (SetoidFunChoice R T' Hequiv Hcompat Hexists) as (f,Hf).
  exists f. firstorder.
Qed.

Theorem simple_setoid_fun_choice_imp_setoid_fun_choice :
  forall A B, SimpleSetoidFunctionalChoice_on A B -> SetoidFunctionalChoice_on A B.
Proof.
  intros A B SimpleSetoidFunChoice R T Hequiv Hcompat Hexists.
  destruct (SimpleSetoidFunChoice R T Hequiv) as (f,Hf); firstorder.
Qed.

Corollary setoid_fun_choice_iff_simple_setoid_fun_choice :
  forall A B, SetoidFunctionalChoice_on A B <-> SimpleSetoidFunctionalChoice_on A B.
Proof.
  split; auto using simple_setoid_fun_choice_imp_setoid_fun_choice, setoid_fun_choice_imp_simple_setoid_fun_choice.
Qed.

(**********************************************************************)
(** ** AC_fun_setoid = AC! + AC_fun_repr                              *)

Theorem setoid_fun_choice_imp_fun_choice :
  forall A B, SetoidFunctionalChoice_on A B -> FunctionalChoice_on A B.
Proof.
  intros A B SetoidFunChoice T Hexists.
  destruct SetoidFunChoice with (R:=@eq A) (T:=T) as (f,Hf).
  - apply eq_equivalence.
  - now intros * ->.
  - assumption.
  - exists f. firstorder.
Qed.

Corollary setoid_fun_choice_imp_functional_rel_reification :
  forall A B, SetoidFunctionalChoice_on A B -> FunctionalRelReification_on A B.
Proof.
  intros A B SetoidFunChoice.
  apply fun_choice_imp_functional_rel_reification.
  now apply setoid_fun_choice_imp_fun_choice.
Qed.

Theorem setoid_fun_choice_imp_repr_fun_choice :
  SetoidFunctionalChoice -> RepresentativeFunctionalChoice .
Proof.
  intros SetoidFunChoice A R Hequiv.
  apply SetoidFunChoice; firstorder.
Qed.

Theorem functional_rel_reification_and_repr_fun_choice_imp_setoid_fun_choice :
  FunctionalRelReification -> RepresentativeFunctionalChoice -> SetoidFunctionalChoice.
Proof.
  intros FunRelReify ReprFunChoice A B R T Hequiv Hcompat Hexists.
  assert (FunChoice : FunctionalChoice).
  { intros A' B'. apply functional_rel_reification_and_rel_choice_imp_fun_choice.
    - apply FunRelReify.
    - now apply repr_fun_choice_imp_relational_choice. }
  destruct (FunChoice _ _ T Hexists) as (f,Hf).
  destruct (ReprFunChoice A R Hequiv) as (g,Hg).
  exists (fun a => f (g a)).
  intro x. destruct (Hg x) as (Hgx,HRuniq).
  split.
  - eapply Hcompat. symmetry. apply Hgx. apply Hf.
  - intros y Hxy. f_equal. auto.
Qed.

Theorem functional_rel_reification_and_repr_fun_choice_iff_setoid_fun_choice :
  FunctionalRelReification /\ RepresentativeFunctionalChoice <-> SetoidFunctionalChoice.
Proof.
  split; intros.
  - now apply functional_rel_reification_and_repr_fun_choice_imp_setoid_fun_choice.
  - split.
    + now intros A B; apply setoid_fun_choice_imp_functional_rel_reification.
    + now apply setoid_fun_choice_imp_repr_fun_choice.
Qed.

(** Note: What characterization to give of
RepresentativeFunctionalChoice? A formulation of it as a functional
relation would certainly be equivalent to the formulation of
SetoidFunctionalChoice as a functional relation, but in their
functional forms, SetoidFunctionalChoice seems strictly stronger *)

(**********************************************************************)
(** * AC_fun_setoid = AC_fun + Ext_fun_repr + EM                      *)

Import EqNotations.

(** ** This is the main theorem in [[Carlström04]] *)

(** Note: all ingredients have a computational meaning when taken in
  separation. However, to compute with the functional choice,
  existential quantification has to be thought as a strong
  existential, which is incompatible with the computational content of
  excluded-middle *)

Theorem fun_choice_and_ext_functions_repr_and_excluded_middle_imp_setoid_fun_choice :
  FunctionalChoice -> ExtensionalFunctionRepresentative -> ExcludedMiddle -> RepresentativeFunctionalChoice.
Proof.
  intros FunChoice SetoidFunRepr EM A R (Hrefl,Hsym,Htrans).
  assert (H:forall P:Prop, exists b, b = true <-> P).
  { intros P. destruct (EM P).
    - exists true; firstorder.
    - exists false; easy. }
  destruct (FunChoice _ _ _ H) as (c,Hc).
  pose (class_of a y := c (R a y)).
  pose (isclass f := exists x:A, f x = true).
  pose (class := {f:A -> bool | isclass f}).
  pose (contains (c:class) (a:A) := proj1_sig c a = true).
  destruct (FunChoice class A contains) as (f,Hf).
  - intros f. destruct (proj2_sig f) as (x,Hx).
    exists x. easy.
  - destruct (SetoidFunRepr A bool) as (h,Hh).
    assert (Hisclass:forall a, isclass (h (class_of a))).
    { intro a. exists a. destruct (Hh (class_of a)) as (Ha,Huniqa).
      rewrite <- Ha. apply Hc. apply Hrefl. }
   pose (f':= fun a => exist _ (h (class_of a)) (Hisclass a) : class).
    exists (fun a => f (f' a)).
    intros x. destruct (Hh (class_of x)) as (Hx,Huniqx). split.
    + specialize Hf with (f' x). unfold contains in Hf. simpl in Hf. rewrite <- Hx in Hf. apply Hc. assumption.
    + intros y Hxy.
       f_equal.
       assert (Heq1: h (class_of x) = h (class_of y)).
       { apply Huniqx. intro z. unfold class_of.
         destruct (c (R x z)) eqn:Hxz.
         - symmetry. apply Hc. apply -> Hc in Hxz. firstorder.
         - destruct (c (R y z)) eqn:Hyz.
           + apply -> Hc in Hyz. rewrite <- Hxz. apply Hc. firstorder.
           + easy. }
       assert (Heq2:rew Heq1 in Hisclass x = Hisclass y).
       { apply proof_irrelevance_cci, EM. }
       unfold f'.
       rewrite <- Heq2.
       rewrite <- Heq1.
       reflexivity.
Qed.

Theorem setoid_functional_choice_first_characterization :
  FunctionalChoice /\ ExtensionalFunctionRepresentative /\ ExcludedMiddle <-> SetoidFunctionalChoice.
Proof.
  split.
  - intros (FunChoice & SetoidFunRepr & EM).
    apply functional_rel_reification_and_repr_fun_choice_imp_setoid_fun_choice.
    + intros A B. apply fun_choice_imp_functional_rel_reification, FunChoice.
    + now apply fun_choice_and_ext_functions_repr_and_excluded_middle_imp_setoid_fun_choice.
  - intro SetoidFunChoice. repeat split.
    + now intros A B; apply setoid_fun_choice_imp_fun_choice.
    + apply repr_fun_choice_imp_ext_function_repr.
       now apply setoid_fun_choice_imp_repr_fun_choice.
    + apply repr_fun_choice_imp_excluded_middle.
       now apply setoid_fun_choice_imp_repr_fun_choice.
Qed.

(**********************************************************************)
(** ** AC_fun_setoid = AC_fun + Ext_pred_repr + PI                    *)

(** Note: all ingredients have a computational meaning when taken in
  separation. However, to compute with the functional choice,
  existential quantification has to be thought as a strong
  existential, which is incompatible with proof-irrelevance which
  requires existential quantification to be truncated *)

Theorem fun_choice_and_ext_pred_ext_and_proof_irrel_imp_setoid_fun_choice :
  FunctionalChoice -> ExtensionalPredicateRepresentative -> ProofIrrelevance -> RepresentativeFunctionalChoice.
Proof.
  intros FunChoice PredExtRepr PI A R (Hrefl,Hsym,Htrans).
  pose (isclass P := exists x:A, P x).
  pose (class := {P:A -> Prop | isclass P}).
  pose (contains (c:class) (a:A) := proj1_sig c a).
  pose (class_of a := R a).
  destruct (FunChoice class A contains) as (f,Hf).
  - intros c. apply proj2_sig.
  - destruct (PredExtRepr A) as (h,Hh).
    assert (Hisclass:forall a, isclass (h (class_of a))).
    { intro a. exists a. destruct (Hh (class_of a)) as (Ha,Huniqa).
      rewrite <- Ha; apply Hrefl. }
    pose (f':= fun a => exist _ (h (class_of a)) (Hisclass a) : class).
    exists (fun a => f (f' a)).
    intros x. destruct (Hh (class_of x)) as (Hx,Huniqx). split.
    + specialize Hf with (f' x). simpl in Hf. rewrite <- Hx in Hf. assumption.
    + intros y Hxy.
       f_equal.
       assert (Heq1: h (class_of x) = h (class_of y)).
       { apply Huniqx. intro z. unfold class_of. firstorder. }
       assert (Heq2:rew Heq1 in Hisclass x = Hisclass y).
       { apply PI. }
       unfold f'.
       rewrite <- Heq2.
       rewrite <- Heq1.
       reflexivity.
Qed.

Theorem setoid_functional_choice_second_characterization :
  FunctionalChoice /\ ExtensionalPredicateRepresentative /\ ProofIrrelevance <-> SetoidFunctionalChoice.
Proof.
  split.
  - intros (FunChoice & ExtPredRepr & PI).
    apply functional_rel_reification_and_repr_fun_choice_imp_setoid_fun_choice.
    + intros A B. now apply fun_choice_imp_functional_rel_reification.
    + now apply fun_choice_and_ext_pred_ext_and_proof_irrel_imp_setoid_fun_choice.
  - intro SetoidFunChoice. repeat split.
    + now intros A B; apply setoid_fun_choice_imp_fun_choice.
    + apply repr_fun_choice_imp_ext_pred_repr.
       now apply setoid_fun_choice_imp_repr_fun_choice.
    + red. apply proof_irrelevance_cci.
       apply repr_fun_choice_imp_excluded_middle.
       now apply setoid_fun_choice_imp_repr_fun_choice.
Qed.

(**********************************************************************)
(** * Compatibility notations *)
Notation description_rel_choice_imp_funct_choice :=
  functional_rel_reification_and_rel_choice_imp_fun_choice (only parsing).

Notation funct_choice_imp_rel_choice := fun_choice_imp_rel_choice (only parsing).

Notation FunChoice_Equiv_RelChoice_and_ParamDefinDescr :=
 fun_choice_iff_rel_choice_and_functional_rel_reification (only parsing).

Notation funct_choice_imp_description := fun_choice_imp_functional_rel_reification (only parsing).

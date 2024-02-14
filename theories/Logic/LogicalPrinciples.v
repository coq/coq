(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Import EqNotations.

(** * Extensionality principles *)

(** See #<a href="./Coq.Logic.ExtensionalityFacts.html">ExtensionalityFacts.v</a># %ExtensionalityFacts.v% *)

Definition FunctionalExtensionality :=
  forall A (B : A -> Type), forall (f g : forall x : A, B x),
    (forall x, f x = g x) -> f = g.

(** Note: Functional extensionality for dependent functions is postulated in [FunctionalExtensionality.v] *)

Definition PropExtensionality :=
  forall (P Q : Prop), (P <-> Q) -> P = Q.

(** Note: Propositional extensionality is postulated in [PropExtensionality.v] *)

(** * Identification principles *)

(** See #<a href="./Coq.Logic.ProofIrrelevance.html">ProofIrrelevanceFacts.v</a># %ProofIrrelevanceFacts.v% *)

(** ** Identity of proofs *)

Definition PropDegeneracy :=
  forall P : Prop, P = True \/ P = False.

Definition ProofIrrelevance :=
  forall (P : Prop) (p1 p2 : P), p1 = p2.

(** Note: Proof irrelevance is postulated in [ProofIrrelevance.v] *)

(** ** Identity of equality proofs *)

(** See [EqdepFacts.v] *)

Definition UniquenessIdentityProofs (A : Type) :=
  forall (x y : A) (e1 : x = y) (e2 : x = y), e1 = e2.

Definition UniquenessIdentityProofsScheme :=
  forall A, UniquenessIdentityProofs A.

Definition UniquenessReflexiveIdentityProofs (A : Type) :=
  forall (x : A) (e : x = x), e = eq_refl.

Definition UniquenessReflexiveIdentityProofsScheme :=
  forall A, UniquenessReflexiveIdentityProofs A.

Definition ReflexiveTransport (A : Type) :=
  forall (x : A) (P : A -> Type) (p : P x) (e : x = x), p = rew [P] e in p.

Definition ReflexiveTransportScheme :=
  forall A, ReflexiveTransport A.

(** Note: Reflexive transport is postulated with name [eq_rect_eq] in [Eqdep.v] *)

(** * Choice principles *)

(** See [ChoiceFacts.v] *)

(** ** Non-choice principles *)

Definition UniqueChoice (A B : Type) :=
  forall (R : A -> B -> Prop),
    (forall x : A, exists! y : B, R x y) -> exists f : A -> B, forall x : A, R x (f x).

Definition UniqueChoiceScheme :=
  forall A B, UniqueChoice A B.

(** Note: Unique choice is also known as no-choice principle *)

(** Note: Unique choice is postulated together with classical logic [ClassicalUniqueChoice.v] *)

Definition DependentUniqueChoice (A : Type) (B : A -> Type) :=
  forall (R : forall x : A, B x -> Prop),
    (forall x : A, exists! y : B x, R x y) -> exists f : (forall x : A, B x), forall x : A, R x (f x).

Definition DependentUniqueChoiceScheme :=
  forall A B, DependentUniqueChoice A B.

(** ** Basic choice principles *)

Definition FunctionalChoice (A B : Type) :=
 forall (R : A -> B -> Prop),
 (forall x : A, exists y : B, R x y) -> exists f : A -> B, forall x : A, R x (f x).

Definition FunctionalChoiceScheme :=
  forall A B, FunctionalChoice A B.

Definition DependentFunctionalChoice (A : Type) (B : A -> Type) :=
  forall (R : forall x : A, B x -> Prop),
  (forall x : A, exists y : B x, R x y) -> exists f : (forall x : A, B x), forall x : A, R x (f x).

Definition DependentFunctionalChoiceScheme :=
  forall (A : Type) (B : A -> Type), DependentFunctionalChoice A B.

Definition FunctionalCountableChoice :=
  forall A, FunctionalChoice nat A.

Definition DependentChoice :=
  forall (A : Type) (R : A -> A -> Prop),
  (forall x : A, exists y, R x y) -> forall x : A, exists f : nat -> A, (f 0 = x /\ forall n, R (f n) (f (S n))).

(** ** Description principles *)

Definition ConstructiveDefiniteDescription :=
  forall (A : Type) (P : A->Prop), (exists! x, P x) -> { x : A | P x }.

(** Note: Constructive definite description is postulated in [Description.v] *)

Definition ConstructiveIndefiniteDescription :=
  forall (A : Type) (P : A->Prop), (exists x, P x) -> { x : A | P x }.

Local Notation inhabited A := A (only parsing).

Definition ClassicalDefiniteDescription :=
  forall (A : Type) (P : A->Prop), inhabited A -> { x : A | (exists! x, P x) -> P x }.

(** Note: Definite description is commonly known as Church's iota *)

Definition ClassicalIndefiniteDescription :=
  forall (A : Type) (P : A->Prop), inhabited A -> { x : A | (exists x, P x) -> P x }.

(** Note: Indefinite description is commonly known as Hilbert's epsilon *)

(** Note: Indefinite description is postulated in [Epsilon.v] *)

(** * Classical principles *)

(** ** Purely logical classical principles *)

Definition DoubleNegationElimination :=
  forall P : Prop, ~ ~ P -> P.

Definition DoubleNegationShift :=
  forall (A : Type) (P : A -> Prop), (forall x : A, ~ ~ P x) -> ~ ~ (forall x, P x).

(** Note: Double Negation Shift is also known as Kuroda principle *)

Definition PeirceLaw :=
  forall P Q : Prop, ((P -> Q) -> P) -> P.

Definition ExcludedMiddle :=
  forall P : Prop, P \/ ~ P.

(** Note: Excluded-middle is postulated in [Classical_Prop.v] *)

Definition WeakExcludedMiddle :=
  forall P : Prop, ~ P \/ ~ ~ P.

Definition ClassicalDeMorganLaw :=
  forall P Q : Prop, ~ (P /\ Q) -> ~ P \/ ~ Q.

Definition GödelDummett :=
  forall P Q : Prop, (P -> Q) \/ (Q -> P).

(** ** Arithmetical classical principles *)

Definition MarkovPrinciple :=
  forall f : nat -> bool, ~ ~ (exists n, f n = true) -> exists n, f n = true.

Definition LimitedPrincipleOmniscience :=
  forall f : nat -> bool, (exists n, f n = true) \/ (forall n, f n <> true).

Definition LesserLimitedPrincipleOmniscience :=
  forall f g : nat -> bool,
  ~ ((exists n, f n = true) /\ (exists n, g n = true)) -> (forall n, f n <> true) \/ (forall n, g n <> true).

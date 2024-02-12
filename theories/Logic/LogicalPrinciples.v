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

Definition FunctionalExtensionality :=
  forall A (B : A -> Type), forall (f g : forall x : A, B x),
    (forall x, f x = g x) -> f = g.

Definition PropExtensionality :=
  forall (P Q : Prop), (P <-> Q) -> P = Q.

(** * Identification principles *)

(** ** Identity of proofs *)

Definition PropDegeneracy :=
  forall P : Prop, P = True \/ P = False.

Definition ProofIrrelevance :=
  forall (P : Prop) (p1 p2 : P), p1 = p2.

(** ** Identity of equality proofs *)

Definition UniquenessIdentityProofs :=
  forall (A : Type) (x y : A) (e1 : x = y) (e2 : x = y), e1 = e2.

Definition UniquenessReflexiveIdentityProofs :=
  forall (A : Type) (x : A) (e : x = x), e = eq_refl.

Definition ReflexiveTransport :=
  forall (A : Type) (x : A) (P : A -> Type) (p : P x) (e : x = x), p = rew [P] e in p.

(** * Choice principles *)

(** ** Non-choice principles *)

Definition UniqueChoice := (** Also known as no-choice principle *)
  forall (A B : Type) (R : A -> B -> Prop),
    (forall x : A, exists! y : B, R x y) -> exists f : A -> B, forall x : A, R x (f x).

Definition DependentUniqueChoice :=
  forall (A : Type) (B : A -> Type) (R : forall x : A, B x -> Prop),
    (forall x : A, exists! y : B x, R x y) -> exists f : (forall x : A, B x), forall x : A, R x (f x).

(** ** Basic choice principles *)

Definition FunctionalChoice :=
 forall (A B : Type) (R : A -> B -> Prop),
 (forall x : A, exists y : B, R x y) -> exists f : A -> B, forall x : A, R x (f x).

Definition DependentFunctionalChoice :=
  forall (A : Type) (B : A -> Type) (R : forall x : A, B x -> Prop),
  (forall x : A, exists y : B x, R x y) -> exists f : (forall x : A, B x), forall x : A, R x (f x).

Definition FunctionalCountableChoice :=
  forall (A : Type) (R : nat -> A -> Prop),
  (forall n, exists y : A, R n y) -> exists f : nat -> A, forall n, R n (f n).

Definition DependentChoice :=
  forall (A : Type) (R : A -> A -> Prop),
  (forall x : A, exists y, R x y) -> forall x : A, exists f : nat -> A, (f 0 = x /\ forall n, R (f n) (f (S n))).

(** ** Description principles *)

Definition ConstructiveDefiniteDescription :=
  forall (A : Type) (P : A->Prop), (exists! x, P x) -> { x : A | P x }.

Definition ConstructiveIndefiniteDescription :=
  forall (A : Type) (P : A->Prop), (exists x, P x) -> { x : A | P x }.

Local Notation inhabited A := A (only parsing).

Definition ClassicalDefiniteDescription := (** Also known as Church's iota *)
  forall (A : Type) (P : A->Prop), inhabited A -> { x : A | (exists! x, P x) -> P x }.

Definition ClassicalIndefiniteDescription := (** Also known as Hilbert's epsilon *)
  forall (A : Type) (P : A->Prop), inhabited A -> { x : A | (exists x, P x) -> P x }.

(** * Classical principles *)

(** ** Purely logical classical principles *)

Definition DoubleNegationElimination :=
  forall P : Prop, ~ ~ P -> P.

Definition DoubleNegationShift := (** Also known as Kuroda principle *)
  forall (A : Type) (P : A -> Prop), (forall x : A, ~ ~ P x) -> ~ ~ (forall x, P x).

Definition PeirceLaw :=
  forall P Q : Prop, ((P -> Q) -> P) -> P.

Definition ExcludedMiddle :=
  forall P : Prop, P \/ ~ P.

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

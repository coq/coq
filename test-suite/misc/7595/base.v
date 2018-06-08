From Coq Require Export Morphisms RelationClasses List Bool Utf8 Setoid.
Set Default Proof Using "Type".
Export ListNotations.
From Coq.Program Require Export Basics Syntax.
Global Generalizable All Variables.

(** * Type classes *)
(** ** Decidable propositions *)
(** This type class by (Spitters/van der Weegen, 2011) collects decidable
propositions. *)
Class Decision (P : Prop) := decide : {P} + {¬P}.
Hint Mode Decision ! : typeclass_instances.
Arguments decide _ {_} : simpl never, assert.

(** ** Proof irrelevant types *)
(** This type class collects types that are proof irrelevant. That means, all
elements of the type are equal. We use this notion only used for propositions,
but by universe polymorphism we can generalize it. *)
Class ProofIrrel (A : Type) : Prop := proof_irrel (x y : A) : x = y.
Hint Mode ProofIrrel ! : typeclass_instances.

Class MGuard (M : Type → Type) :=
  mguard: ∀ P {dec : Decision P} {A}, (P → M A) → M A.
Arguments mguard _ _ _ !_ _ _ / : assert.
Notation "'guard' P ; z" := (mguard P (λ _, z))
  (at level 20, z at level 200, only parsing, right associativity) .
Notation "'guard' P 'as' H ; z" := (mguard P (λ H, z))
  (at level 20, z at level 200, only parsing, right associativity) .

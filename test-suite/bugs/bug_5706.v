From Corelib.ssr Require Import ssreflect.
From Corelib Require Import RelationClasses Relation_Definitions Setoid.

Parameter P : nat -> Prop.
Parameter f : nat -> nat.
Parameter foo_eq : forall x, P 0 -> P 1 -> x = f x.

Axiom p0 : P 0.
Axiom p1 : P 1.

Goal 0 = f 0.
Proof.
  rewrite -(foo_eq 0); [ exact: p0 | exact: p1 | reflexivity ].
Abort.


Parameter R : relation nat.
Parameter R_equivalence : Equivalence R.
#[global] Existing Instance R_equivalence.

Parameter foo_R : forall x, P 0 -> P 1 -> R x (f x).

Goal R 0 (f 0).
Proof.
  rewrite -(foo_R 0); [ exact: p0 | exact: p1 | apply: Equivalence_Reflexive ].
Abort.

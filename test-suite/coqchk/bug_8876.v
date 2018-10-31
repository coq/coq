(* -*- coq-prog-args: ("-noinit"); -*- *)
Require Import Coq.Init.Notations.

Notation "x -> y" := (forall _ : x, y).

Inductive eq {A:Type} (a:A) : A -> Prop := eq_refl : eq a a.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Printing Universes.

(* Constructors for an inductive with indices *)
Module WithIndex.
  Inductive foo@{i} : (Prop -> Prop) -> Prop := mkfoo: foo (fun x => x).

  Monomorphic Universes i j.
  Monomorphic Constraint i < j.
  Definition bar : eq mkfoo@{i} mkfoo@{j} := eq_refl _.
End WithIndex.

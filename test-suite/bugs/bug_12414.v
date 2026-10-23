Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Printing Universes.
Inductive list {T} : Type := | cons (t : T) : list -> list. (* who needs nil anyway? *)
Arguments list : clear implicits.
Section map.
  Context {A B : Type}.
  Fixpoint map (f: A -> B) (l : list A) : list B :=
  let '(cons t l) := l in cons (f t) (map f l).
End map. About map@{_ _}.
(* Two universes, as expected. *)

Definition map_Set@{} {A B : Set} := @map A B.
Definition map_Prop@{} {A B : Prop} := @map A B.

Module MapNoSec.
  Fixpoint map {A B : Type} (f: A -> B) (l : list A) : list B :=
    let '(cons t l) := l in cons (f t) (map f l).

  About map@{_ _}.
  Definition map_Set (A B : Set) := @map A B.
  Definition map_Prop {A B : Prop} := @map A B.
  Check map_Set@{}.
  Check map_Prop@{}.
End MapNoSec.

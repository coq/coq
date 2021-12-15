Set Universe Polymorphism.
Set Printing Universes.
Inductive list {T} : Type := | cons (t : T) : list -> list. (* who needs nil anyway? *)
Arguments list : clear implicits.

Fixpoint map {A B} (f: A -> B) (l : list A) : list B :=
  let '(cons t l) := l in cons (f t) (map f l).
About map@{_ _}.
(* Two universes, as expected. *)

Definition map_Set@{} {A B : Set} := @map A B.

Definition map_Prop@{} {A B : Prop} := @map A B.

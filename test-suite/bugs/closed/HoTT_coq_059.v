(* -*- mode: coq; coq-prog-args: ("-indices-matter") -*- *)
Set Universe Polymorphism.

Inductive eq {A} (x : A) : A -> Type := eq_refl : eq x x.
Notation "a = b" := (eq a b) : type_scope.

Section foo.
  Class Funext := { path_forall :> forall A P (f g : forall x : A, P x), (forall x, f x = g x) -> f = g }.
  Context `{Funext, Funext}.

  Set Printing Universes.

  (** Typeclass resolution should pick up the different instances of Funext automatically *)
  Definition foo := (@path_forall _ _ _ (@path_forall _ Set)).
  (* Toplevel input, characters 0-60:
Error: Universe inconsistency (cannot enforce Top.24 <= Top.23 because Top.23
< Top.22 <= Top.24). *)

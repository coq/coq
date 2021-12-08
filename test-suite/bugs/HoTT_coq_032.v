Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Delimit Scope object_scope with object.
Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Delimit Scope functor_scope with functor.

Local Open Scope category_scope.

Record SpecializedCategory (obj : Type) :=
  {
    Object :> _ := obj;
    Morphism : obj -> obj -> Type;

    Compose : forall s d d', Morphism d d' -> Morphism s d -> Morphism s d'
  }.
(* Anomaly: Mismatched instance and context when building universe substitution.
Please report. *)

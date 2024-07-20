From Stdlib Require Import PrimInt63.

Set Universe Polymorphism.

Primitive array := #array_type.

Primitive make : forall A, int -> A -> array A := #array_make.
Arguments make {_} _ _.

Primitive get : forall A, array A -> int -> A := #array_get.
Arguments get {_} _ _.

Primitive default : forall A, array A -> A:= #array_default.
Arguments default {_} _.

Primitive set : forall A, array A -> int -> A -> array A := #array_set.
Arguments set {_} _ _ _.

Primitive length : forall A, array A -> int := #array_length.
Arguments length {_} _.

Primitive copy : forall A, array A -> array A := #array_copy.
Arguments copy {_} _.

Module Export PArrayNotations.

Declare Scope array_scope.
Delimit Scope array_scope with array.
Notation "t .[ i ]" := (get t i)
  (at level 2, left associativity, format "t .[ i ]").
Notation "t .[ i <- a ]" := (set t i a)
  (at level 2, left associativity, format "t .[ i <- a ]").

End PArrayNotations.

Primitive max_length := #array_max_length.

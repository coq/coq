Require Import PrimArray.
Universes u v.

Definition a : array@{v} nat := [| | 0 |]@{u}.

Definition b : array@{v} _ := [| | 0 |]@{u}.

Constraint u < v.

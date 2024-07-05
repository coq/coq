Require Import Ltac2.Constr Ltac2.Init Ltac2.Control.
Import Unsafe.

Ltac2 Eval match (kind '(nat -> bool)) with
           | Prod a c => a
           | _ => throw Match_failure end.

Set Allow StrictProp.
Axiom something : SProp.
Ltac2 Eval match (kind '(forall x : something, bool)) with
           | Prod a c => a
           | _ => throw Match_failure end.

From Stdlib Require Import PrimInt63 PrimArray.
Open Scope array_scope.
Ltac2 Eval match (kind '([|true|true|])) with
  | Array _ _ _ ty => ty
  | _ => throw Match_failure end.

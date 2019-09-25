Require Import Ltac2.Constr Ltac2.Init Ltac2.Control.
Import Unsafe.

Ltac2 Eval match (kind '(nat -> bool)) with
           | Prod a b c => a
           | _ => throw Match_failure end.

Set Allow StrictProp.
Axiom something : SProp.
Ltac2 Eval match (kind '(forall x : something, bool)) with
           | Prod a b c => a
           | _ => throw Match_failure end.

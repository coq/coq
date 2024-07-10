(* This was failing at parsing *)

Notation "'a'" := tt (only printing).
Goal True. let a := constr:(1+1) in idtac a. Abort.

(* Idem *)

From Stdlib Require Import String.
From Stdlib Require Import ZArith.
Open Scope string_scope.

Axiom Ox: string -> Z.

Axiom isMMIOAddr: Z -> Prop.

Notation "'Ox' a" := (Ox a) (only printing, at level 10, format "'Ox' a").

Goal False.
  set (f := isMMIOAddr).
  set (x := f (Ox "0018")).
Abort.

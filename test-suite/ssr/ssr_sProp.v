Require Import ssreflect.

Inductive sEmpty : SProp :=.

Goal True.
have h := (fun x : sEmpty => x).
constructor.
Qed.

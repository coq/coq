Require Import ssreflect.
From Ltac2 Require Import Ltac2.

Inductive nat_list :=
  Nil
| Cons of nat & nat_list.

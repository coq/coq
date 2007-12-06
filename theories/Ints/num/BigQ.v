Require Export QMake_base.
Require Import QpMake.
Require Import QvMake.
Require Import Q0Make.
Require Import QifMake.
Require Import QbiMake.

(* We choose for Q the implemention with
   multiple representation of 0: 0, 1/0, 2/0 etc *)
Module BigQ := Q0.

Definition bigQ := BigQ.t.

Delimit Scope bigQ_scope with bigQ.
Bind Scope bigQ_scope with bigQ.
Bind Scope bigQ_scope with BigQ.t.

Notation " i + j " := (BigQ.add i j) : bigQ_scope.
Notation " i - j " := (BigQ.sub i j) : bigQ_scope.
Notation " i * j " := (BigQ.mul i j) : bigQ_scope.
Notation " i / j " := (BigQ.div i j) : bigQ_scope.
Notation " i ?= j " := (BigQ.compare i j) : bigQ_scope.


(* We check that various definitions or lemmas have the correct
   argument scopes, especially the ones created via functor application. *)

Close Scope nat_scope.

Require Import PArith.
Check (Pos.add 1 2).
Check (Pos.add_comm 1 2).
Check (Pos.min_comm 1 2).
Definition f_pos (x:positive) := x.
Definition f_pos' (x:Pos.t) := x.
Check (f_pos 1).
Check (f_pos' 1).

Require Import ZArith.
Check (Z.add 1 2).
Check (Z.add_comm 1 2).
Check (Z.min_comm 1 2).
Definition f_Z (x:Z) := x.
Definition f_Z' (x:Z.t) := x.
Check (f_Z 1).
Check (f_Z' 1).

Require Import NArith.
Check (N.add 1 2).
Check (N.add_comm 1 2).
Check (N.min_comm 1 2).
Definition f_N (x:N) := x.
Definition f_N' (x:N.t) := x.
Check (f_N 1).
Check (f_N' 1).

Require Import Arith.
Check (Nat.add 1 2).
Check (Nat.add_comm 1 2).
Check (Nat.min_comm 1 2).
Definition f_nat (x:nat) := x.
Definition f_nat' (x:Nat.t) := x.
Check (f_nat 1).
Check (f_nat' 1).

Require Import BigN.
Check (BigN.add 1 2).
Check (BigN.add_comm 1 2).
Check (BigN.min_comm 1 2).
Definition f_bigN (x:bigN) := x.
Check (f_bigN 1).

Require Import BigZ.
Check (BigZ.add 1 2).
Check (BigZ.add_comm 1 2).
Check (BigZ.min_comm 1 2).
Definition f_bigZ (x:bigZ) := x.
Check (f_bigZ 1).

Require Import BigQ.
Check (BigQ.add 1 2).
Check (BigQ.add_comm 1 2).
Check (BigQ.min_comm 1 2).
Definition f_bigQ (x:bigQ) := x.
Check (f_bigQ 1).
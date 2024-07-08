From Ltac2 Require Import Ltac2.
From Ltac2ssr Require Import Ipat.
Require Import ssreflect.

Ltac2 @ external move_up : ipat list -> unit := "coq-core.plugins.ltac2ssr" "move_up".

(* move=> <il> *)
Ltac2 Notation "move_up" il(ipats) := move_up il.

Goal nat -> bool -> False.
ltac1:(move=> + x).
Show.
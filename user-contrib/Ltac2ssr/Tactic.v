Require Import Ltac2.
From Ltac2ssr Require Import Ipat.

Ltac @ external move_up : list(ipat) -> unit := "coq-core.plugins.ltac2ssr" "move_up".

(* move=> <il> *)
Ltac2 Notation "move_up" il(list1(ipat)) := move_up il.

Goal nat -> False.
move_up x.
Show.
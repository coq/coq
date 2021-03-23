Require Import Ltac2.Ltac2.

Ltac2 foo0 x y : unit := ().
Ltac2 foo1 : unit := ().
Fail Ltac2 foo2 : unit -> unit := ().
Ltac2 foo3 : unit -> unit := fun (_ : unit) => ().

Ltac2 bar0 := fun x y : unit => ().
Fail Ltac2 bar1 := fun x : unit => 0.
Ltac2 bar2 := fun x : unit list => [].

Ltac2 qux0 := let x : unit := () in ().
Ltac2 qux1 () := let x y z : unit := () in x 0 "".
Fail Ltac2 qux2 := let x : unit -> unit := () in ().

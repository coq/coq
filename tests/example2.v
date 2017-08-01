Require Import Ltac2.Ltac2.

Ltac2 Notation "split" bnd(bindings) := Std.split bnd.

Goal exists n, n = 0.
Proof.
split with (x := 0).
Std.reflexivity ().
Qed.

Goal exists n, n = 0.
Proof.
split with 0.
split.
Qed.

Goal exists n, n = 0.
Proof.
let myvar := Std.NamedHyp @x in split with (?myvar := 0).
split.
Qed.

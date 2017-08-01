Require Import Ltac2.Ltac2.

Import Ltac2.Notations.

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

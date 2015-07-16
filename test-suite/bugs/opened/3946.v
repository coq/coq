Require Import ZArith.

Inductive foo := Foo : Z.le 0 1 -> foo.

Definition bar (f : foo) := let (f) := f in f.

(* Doesn't work: *)
(* Arguments bar f.*)

(* Does work *)
Arguments bar f _.

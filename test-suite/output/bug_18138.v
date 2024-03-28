Require Import Ltac2.Ltac2.

Module Import M.
  Ltac2 foo := ().
End M.

#[warnings="-ltac2-unused-variable"]
Ltac2 bar foo := M.foo.

Print bar.
(* was fun foo => foo *)

(* sadly this is still incorrect *)
Ltac2 baz foo := constr:(ltac2:(foo M.foo)).

Print baz.

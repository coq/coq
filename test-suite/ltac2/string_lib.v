Require Import Ltac2.Ltac2.

Ltac2 Type exn ::= [ Failure ].

Ltac2 check (b : bool) :=
  if b then () else Control.throw Failure.

Ltac2 Eval
  let s := "Hello, world!" in
  let hello := String.sub s 0 5 in
  check (String.equal hello "Hello").

Fail Ltac2 Eval String.sub "" 2 2.

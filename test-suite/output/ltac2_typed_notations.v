Require Import Ltac2.Ltac2.

Fail Ltac2 foo(b: bool): bool :=
  let c := b in
  match! c with
  | true => true
  | false => false
  end.
(* error used to be on the whole command *)

Ltac2 Globalize fun (b: bool) =>
  (let c := b in
  match! c with
  | true => true
  | false => false
  end : bool).

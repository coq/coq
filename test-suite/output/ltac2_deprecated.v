Require Import Ltac2.Ltac2.

#[deprecated(note="test_definition")]
Ltac2 foo := ().

#[deprecated(note="test_notation")]
Ltac2 Notation bar := ().

#[deprecated(note="test_external")]
Ltac2 @ external qux : 'a array -> int := "rocq-runtime.plugins.ltac2" "array_length".
(* Randomly picked external function *)

Ltac2 Eval foo.
Ltac2 Eval bar.
Ltac2 Eval qux.

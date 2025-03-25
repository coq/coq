(* -*- coq-prog-args: ("-noinit"); -*- *)

Require Import Ltac2.Ltac2.

Fail Check Corelib.Init.Logic.True.

Require Import Corelib.Init.Logic.

Check Corelib.Init.Logic.True.

Goal True.
  Fail now ().
Abort.

Require Corelib.Init.Tactics.

Goal True.
  now ().
Qed.

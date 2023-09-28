From Ltac2 Require Import Ltac2.

Ltac2 f () := Control.zero (Invalid_argument None).

Goal True.
Proof.
  Set Ltac2 Backtrace.
  Fail Control.plus f (fun e => Control.zero e).
  Fail Control.plus f (fun e => Control.throw e).
  Fail Control.plus_bt f (fun e bt => Control.zero_bt e bt).
  Fail Control.plus_bt f (fun e bt => Control.throw_bt e bt).
Abort.

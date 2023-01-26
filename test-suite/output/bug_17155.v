From Ltac2 Require Import Ltac2.
Module M.
  #[local] Ltac2 f () := Control.throw (Invalid_argument None).
  Ltac2 g () := f ().
End M.
Fail Ltac2 Eval M.g ().         (* Fails, as expected. *)
Set Ltac2 Backtrace.
Fail Ltac2 Eval M.g ().         (* Anomaly "Uncaught exception Not_found." *)
Print M.g.

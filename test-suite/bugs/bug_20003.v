Require Import Corelib.Strings.PrimString.
Definition t (s : string) := True.
Arguments t !_ /.
Goal t "test".
Proof.
  progress cbn.
Abort.

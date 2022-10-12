Require Import Ltac2.Ltac2.

Fail Ltac2 foo () := () ().

Fail Ltac2 foo () := ((), ()) ().

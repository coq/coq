From Stdlib Require Import Uint63 PArray.
Definition t : array nat := [| 1; 3; 2 | 4 |].
Definition vm_accu_set v := Eval vm_compute in t.[1 <- v].

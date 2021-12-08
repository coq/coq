(* These calls were raising an anomaly at some time *)
Inductive A : nat -> id (nat->Type) := .
Eval vm_compute in fun x => match x in A y z return y = z with end.
Eval native_compute in fun x => match x in A y z return y = z with end.

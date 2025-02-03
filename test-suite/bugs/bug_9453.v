(* check compatibility with 8.8 and earlier for lack of warnings on the nat 5000 *)
Set Warnings "+large-nat,+abstract-large-number".
Fail Check 5001.
Check 5000.
(* Error:
To avoid stack overflow, large numbers in nat are interpreted as applications of
Nat.of_uint. *)

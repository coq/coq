(* Check Guard in proofs *)

Goal nat->nat.
fix f 1.
intro n; apply f; assumption.
Fail Guarded.

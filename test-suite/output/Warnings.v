(* Term in warning was not printed in the right environment at some time *)
Record A := { B:Type; b:Prop }.
Definition a B := {| B:=B; b:=forall x, x > 0 |}.
Canonical Structure a.


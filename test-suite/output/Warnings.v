(* Term in warning was not printed in the right environment at some time *)
Record A := { B:Type; b:Prop }.
Definition a B := {| B:=B; b:= let _ := tt in True |}.
Canonical Structure a.


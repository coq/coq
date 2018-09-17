(* Term in warning was not printed in the right environment at some time *)
#[universes(template)] Record A := { B:Type; b:B->B }.
Definition a B := {| B:=B; b:=fun x => x |}.
Canonical Structure a.


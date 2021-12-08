Record C {PROP: Prop} (P : PROP) : Type := { c : unit}.
Check fun '{|c:=x|} => tt.      (* Fine *)
Arguments Build_C {_ _} _.
Check fun '(Build_C _) => tt. (* Works. Note: just 1 argument! *)
Check fun '{|c:=x|} => tt.
(* Error: The constructor @Build_C (in type @C) expects 1 argument. *)

Set Asymmetric Patterns.
Check fun '{|c:=x|} => tt.

Set Primitive Projections.
Set Warnings "+non-primitive-record".

(* 0 fields *)
Fail Record foo := { a := 0 }.

(* anonymous field *)
Fail Record foo := { _ : nat }.

(* squashed *)
Fail Record foo : Prop := { a : nat }.

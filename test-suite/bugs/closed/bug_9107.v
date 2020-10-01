(* Occur-check issue *)
Set Primitive Projections.
Class A (x : unit) := { T : Set; x : T }.
Unset Primitive Projections.
Record B {a : A tt} := { P u := unit; _ : P x -> x = x }.

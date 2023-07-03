Inductive foo := Foo ( foop : bar )
with bar := Bar ( barp : foo ).

Check (foo, bar) : Prop * Prop.
(* Set * Prop *)

Check fun b : bar => match b with Bar x => x end.
(* incorrect elimination to return sort Set *)

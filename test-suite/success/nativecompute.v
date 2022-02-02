(* An example with local definitions *)

Inductive I (a:=0) (b:nat) (c:=1) := C : I b.

Eval native_compute in (fun x => C) 0.

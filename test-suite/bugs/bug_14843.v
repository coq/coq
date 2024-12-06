(* f1 was renamed into Coq__1.f1 but Coq__1 was not defined *)
(* similar to #12813, #16677 *)

Record r : Type := mk { f1 : unit -> unit; f2: unit -> unit }.
Set Primitive Projections.
Record r' : Type := mk' { f1' : unit -> unit; f2': unit -> unit }.
Unset Primitive Projections.

Module M.
Definition f1 (ti:unit) : unit := tt.
Definition f2 (ti:unit) : unit := tt.
Definition cf := mk f1 f2.

Definition f1' (ti:unit) : unit := tt.
Definition f2' (ti:unit) : unit := tt.
Definition cf' := mk' f1' f2'.
End M.

Require Import Corelib.extraction.Extraction.
Recursive Extraction M.cf M.cf'.
Extraction TestCompile M.cf M.cf'.

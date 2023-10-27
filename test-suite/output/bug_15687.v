Require Import Ltac2.Ltac2.

Fail Ltac2 rec foo(i: int)(j: int) :=
  foo i (bar j)
(*^^^*)
with bar(i: int) :=
  Int.add (foo i (*i*)) 1.

Fail Ltac2 rec bar(i: int) :=
  Int.add (foo i (*i*)) 1
with foo(i: int)(j: int) : bool :=
    foo i (bar j).

(* The location is not great if we write "fun x y => x" but that's
   unrelated to what we're testing here.

  Also the toplevel "Ltac2 rec foo :=" is currently not smart enough to recognize a function with type annotation. *)
Fail Ltac2 foo := let rec foo : int -> int := fun x => fun y => x in foo.

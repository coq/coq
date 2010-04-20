(* Check that destruct refreshes universes in what it generalizes *)

Section test.

Variable A: Type.

Inductive T: unit -> Type := C: A -> unit -> T tt.

Let unused := T tt.

Goal T tt -> False.
 intro X.
 destruct X.

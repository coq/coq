(* Scheme Equality not robust wrt names *)

Module A1.
  Inductive A (T : Type) := C (a : T).
  Scheme Equality for A. (* success *)
End A1.

Module A2.
  Inductive A (x : Type) := C (a : x).
  Scheme Equality for A. 
End A2.

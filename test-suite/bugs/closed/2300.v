(* Check some behavior of Ltac pattern-matching wrt universe levels *)

Section contents.

Variables (A: Type) (B: (unit -> Type) -> Type).

Inductive C := c: A -> unit -> C.

Let unused2 (x: unit) := C.

Goal True.
intuition.
Qed.

End contents.

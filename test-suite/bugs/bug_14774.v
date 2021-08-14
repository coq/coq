Parameter A : nat -> Set.
Parameter f : forall n, A n -> A n.
Inductive I := C : unit -> I.

Check (let (_) := C tt in f _ _).
(* was: Cannot infer the return type of pattern-matching on "C tt". *)

(* Print Assumptions reuses traversals across queries in one environment.
   A dependency shared by two children is reached first through one child;
   a later query on the other child must still report it. *)

Axiom C : nat.
Definition A := C.
Definition B := C.
Definition R := A + B.
Print Assumptions R.
Print Assumptions B.
Print Assumptions A.
Print Assumptions B R.

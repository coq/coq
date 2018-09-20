(* Examples of use of Scheme Equality *)

Module A.
Definition N := nat.
Inductive list := nil | cons : N -> list -> list.
Scheme Equality for list.
End A.

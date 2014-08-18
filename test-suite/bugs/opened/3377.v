Set Primitive Projections.
Set Implicit Arguments.
Record prod A B := pair { fst : A; snd : B}.

Goal fst (@pair Type Type Type Type).
Set Printing All.
Fail match goal with |- ?f _ => idtac end.
(* Toplevel input, characters 7-44:
Error: No matching clauses for match. *)

(* Implicit on section variables *)
(* Example submitted by David Nowak *)

Set Implicit Arguments.
Section Spec.
Variable A:Set.
Variable op : (A:Set)A->A->Set.
Infix 6 "#" op.
Check (x:A)(x # x).

Notation D1 := (forall {T : Type} ( x : T ) , Type).

Definition DD1 ( A : forall {T : Type} (x : T), Type ) := A 1.
Fail Definition DD1' ( A : D1 ) := A 1. (* Toplevel input, characters 32-33:
Error: In environment
A : forall T : Type, T -> Type
The term "1" has type "nat" while it is expected to have type
"Type".
 *)

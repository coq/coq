Set Printing Universes.

Fixpoint CardinalityRepresentative (n : nat) : Set :=
  match n with
    | O => Empty_set
    | S n' => sum (CardinalityRepresentative n') unit
  end.
(* Toplevel input, characters 104-143:
Error:
In environment
CardinalityRepresentative : nat -> Set
n : nat
n' : nat
The term "(CardinalityRepresentative n' + unit)%type" has type
 "Type (* max(Top.73, Top.74) *)" while it is expected to have type
"Set". *)

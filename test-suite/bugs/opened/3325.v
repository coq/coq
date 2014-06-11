Axiom SProp : Set.
Axiom sp : SProp.

(* If we hardcode valueType := nat, it goes through *)
Class StateIs := {
  valueType : Type;
  stateIs : valueType -> SProp
}.

Instance NatStateIs : StateIs := {
  valueType := nat;
  stateIs := fun _ => sp
}.

Class LogicOps F := { land: F -> F }.
Instance : LogicOps SProp. Admitted.
Instance : LogicOps Prop. Admitted.

Set Printing All.
Parameter (n : nat).
(* If this is a [Definition], the resolution goes through fine. *)
Notation vn := (@stateIs _ n).
Definition vn' := (@stateIs _ n).
Definition GOOD : SProp :=
  @land _ _ vn'.
(* This doesn't resolve, if PropLogicOps is defined later than SPropLogicOps *)
Fail Definition BAD : SProp :=
  @land _ _ vn.

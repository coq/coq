Typeclasses eauto := debug.
Set Printing All.

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
Canonical Structure NatStateIs.

Class LogicOps F := { land: F -> F }.
Instance : LogicOps SProp. Admitted.
Instance : LogicOps Prop. Admitted.

Parameter (n : nat).
(* If this is a [Definition], the resolution goes through fine. *)
Notation vn := (@stateIs _ n).
Definition vn' := (@stateIs _ n).
Definition GOOD : SProp :=
  @land _ _ vn'.
(* This doesn't resolve, if PropLogicOps is defined later than SPropLogicOps *)
Definition BAD : SProp :=
  @land _ _ vn.


Class A T := { foo : T -> Prop }.
Instance: A nat. Admitted.
Instance: A Set. Admitted.

Class B := { U : Type ; b : U }.
Instance bi: B := {| U := nat ; b := 0 |}.
Canonical Structure bi.

Notation b0N := (@b _ : nat).
Notation b0Ni := (@b bi : nat).
Definition b0D := (@b _ : nat).
Definition GOOD1 := (@foo _ _ b0D).
Definition GOOD2 := (let x := b0N in @foo _ _ x).
Definition GOOD3 := (@foo _ _ b0Ni).
Definition BAD1 := (@foo _ _ b0N). (* Error: The term "b0Ni" has type "nat" while it is expected to have type "Set". *)

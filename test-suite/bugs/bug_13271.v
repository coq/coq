Require Program.Tactics.

Definition PeanoWithMax (maxValue : nat) : Set := { value : nat | value <= maxValue }.

Polymorphic Definition NonEmptyList (elementType : Type) : Type :=
  { list : list elementType | list <> nil }.

Axiom n : nat.
Axiom ListFromPeano : forall (value : nat), list (PeanoWithMax n).

Polymorphic Program Definition FromPeano (value : nat) : NonEmptyList (PeanoWithMax n) :=
  match value with
  | 0 => exist _ (cons (exist _ 0 _) nil) _
  | S _ => exist _ (ListFromPeano value) _
  end.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

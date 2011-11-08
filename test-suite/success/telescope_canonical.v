Structure Inner := mkI { is :> Type }.
Structure Outer := mkO { os :> Inner }.

Canonical Structure natInner := mkI nat.
Canonical Structure natOuter := mkO natInner.

Definition hidden_nat := nat.

Axiom P : forall S : Outer, is (os S) -> Prop.

Lemma foo (n : hidden_nat) : P _ n.
Admitted.

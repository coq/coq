Set Printing Universes.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Record Unit : Prop := tt {}.

Record Foo (A B : Type) : Prop := mkfoo { }.

Parameter V : Type -> Type.
Axiom foobar : forall A, V A -> Foo@{_ Set} A Unit.

Section sec.
  Universe a.
  Variable A : Type@{a}.
  Variable v : V A.

  Definition bar@{i|a <= i} : Foo@{i i} A Unit.
  Proof.
    apply foobar.
    apply v.
  Qed.
End sec.

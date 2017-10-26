Universes i.

Fail Constraint i < Set.
Fail Constraint i <= Set.
Fail Constraint i = Set.
Constraint Set <= i.
Constraint Set < i.
Fail Constraint i < j. (* undeclared j *)
Fail Constraint i < Type. (* anonymous *)

Set Universe Polymorphism.

Section Foo.
  Universe j.
  Constraint Set < j.

  Definition foo := Type@{j}.
End Foo.

Set Implicit Arguments.
Set Universe Polymorphism.

Module success.
  Unset Primitive Projections.

  Record group :=
    { carrier : Type;
      id : carrier }.

  Notation "1" := (id _) : g_scope.

  Delimit Scope g_scope with g.
  Bind Scope g_scope with carrier.

  Section foo.
    Variable g : group.
    Variable comp : carrier g -> carrier g -> carrier g.

    Check comp 1 1.
  End foo.
End success.

Module failure.
  Set Primitive Projections.

  Record group :=
    { carrier : Type;
      id : carrier }.

  Notation "1" := (id _) : g_scope.

  Delimit Scope g_scope with g.
  Bind Scope g_scope with carrier.

  Section foo.
    Variable g : group.
    Variable comp : carrier g -> carrier g -> carrier g.

    Check comp 1 1.
    (* Toplevel input, characters 11-12:
Error:
In environment
g : group
comp : carrier g -> carrier g -> carrier g
The term "1" has type "nat" while it is expected to have type "carrier g".
    *)
  End foo.
End failure.

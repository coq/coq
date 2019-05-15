Declare Scope foo_scope.
Declare Scope bar_scope.

Axiom T : Type.
Axiom x : T.

Notation "!!" := x : foo_scope.
Notation "##" := x : bar_scope.

Bind Scope foo_scope with T.
Definition def (x : T) := x.
Bind Scope bar_scope with T.

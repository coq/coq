
Polymorphic Axiom foo@{u v | u < v} : Type@{v}.

Unset Universe Checking.
Type foo@{Set Set}.

Polymorphic Definition castU@{u v |}(t: Type@{u}): Type@{v} := t.

Set Universe Checking.

Polymorphic Definition bar@{u v|} : Type@{u} -> Type@{v} := castU@{u v}.

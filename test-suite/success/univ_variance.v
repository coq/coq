Set Universe Polymorphism.

Definition foo@{+i} := Type@{i}.

Definition bar := foo.

Definition contra@{-i} := Type@{i} -> False.

Set Debug "univMinim".

Definition contra_pos@{+i} := (contra@{i} -> False).

Definition sid@{s | *i |} (A : Type@{s|i}) (a : A) := a.

Definition foobar (P : Prop) := sid@{_|_} P.

Definition foobar'@{i} (A : Type@{i}) := sid@{Type|_} A.

Cumulative Inductive eq@{s s'|*i +i'| } (A : Type@{s|i}) (a : A) : A -> Type@{s'|i'} :=
  eq_refl : eq A a a.

Definition foo' := (eq@{Type Prop|_ _} nat 0 1).
Definition foo'' := (eq@{Type Prop|_ _} Set nat bool).

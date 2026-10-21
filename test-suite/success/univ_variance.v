Set Universe Polymorphism.
Set Polymorphic Definitions Cumulativity.
Definition foo@{+i} := Type@{i}.

Definition bar := foo.

Definition contra@{i} := Type@{i} -> False.

Definition contra_pos@{i} := (contra@{i} -> False).

Definition sid@{s | i |} (A : Type@{s|i}) (a : A) := a.

Definition foobar (P : Prop) := sid@{Prop|_} P.

Definition foobar'@{i} (A : Type@{i}) := sid A.

Definition foobar'' A := sid A.
(* Same as the annotated version *)

Cumulative Inductive eq@{s s'; i i'} (A : Type@{s|i}) (a : A) : A -> Type@{s'|i'} :=
  eq_refl : eq A a a.

Definition foo' := (eq@{Type Prop;_ _} nat 0 1).
Check foo'@{}.
Definition foo'' := (eq@{Type Prop;_ _} Set nat bool).
Check foo''@{}.

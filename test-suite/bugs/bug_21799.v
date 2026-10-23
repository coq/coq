Module SP.
  Inductive sTrue : SProp := sI.
  Class Foo (x : SProp) : SProp := foo : x.
  Definition Bar := Foo sTrue.
  Identity Coercion Bar_to_Foo : Bar >-> Foo.
(* Binder (x : "Bar") has relevance mark set to relevant but was expected to be irrelevant
(maybe a bugged tactic). *)
End SP.

Module Poly.
  Set Universe Polymorphism.
  Unset Collapse Sorts ToType.
  Unset Polymorphic Inductive Cumulativity.
  Inductive pTrue : Univ := pI.

  (* sanity check instance length *)
  Check pTrue@{_;_}.

  Class Foo (x : Univ) : Type := foo : x.
  Definition Bar := Foo pTrue.

  (* sanity check instance length *)
  Check Bar@{_;_}.

  Identity Coercion Bar_to_Foo : Bar >-> Foo.

  Type Bar_to_Foo@{SProp;_} : Bar@{SProp;_} -> Foo@{SProp;_} pTrue@{SProp;_}.
  Type Bar_to_Foo@{Type;_} : Bar@{Type;_} -> Foo@{Type;_} pTrue@{Type;_}.
End Poly.

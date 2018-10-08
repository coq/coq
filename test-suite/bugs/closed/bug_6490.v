Inductive Foo (A' := I) (B : Type) := foo : Foo B.

Goal Foo True. dtauto. Qed.
Goal Foo True. firstorder. Qed.

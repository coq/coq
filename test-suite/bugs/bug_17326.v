Set Primitive Projections.

Inductive sTrue : SProp := sI.

Inductive Foo : SProp := Mk { x : sTrue }.

Type (fun (P:Foo -> Type) => @Foo_rect P).

Inductive T := Foo : T.
Axiom (b : T) (R : forall x : T, Prop) (f : forall x : T, R x).
Axiom a1 : match b with Foo => f end = f.
Axiom a2 : match b with Foo => f b end = f b.
Hint Rewrite a1 a2 : bar.

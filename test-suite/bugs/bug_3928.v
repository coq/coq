Typeclasses eauto := (bfs).

Class Foo := {}.
Class Bar := {}.

Instance: Bar := {}.
Instance: Foo -> Bar -> Foo -> Foo | 1 := {}.
Instance: Bar -> Foo | 100 := {}.
Instance: Foo -> Bar -> Foo -> Foo | 1 := {}.

Check (_ : Foo). (* timeout *)

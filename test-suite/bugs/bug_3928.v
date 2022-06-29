Typeclasses eauto := (bfs).

Class Foo := {}.
Class Bar := {}.

#[export] Instance: Bar := {}.
#[export] Instance: Foo -> Bar -> Foo -> Foo | 1 := {}.
#[export] Instance: Bar -> Foo | 100 := {}.
#[export] Instance: Foo -> Bar -> Foo -> Foo | 1 := {}.

Check (_ : Foo). (* timeout *)

Inductive foo := Foo : False -> foo.
Goal foo.
try (constructor ; fail 0).
Fail try (constructor ; fail 1).

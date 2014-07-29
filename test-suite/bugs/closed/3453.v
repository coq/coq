Set Primitive Projections.
Record Foo := { bar : Set }.
Class Baz (F : Foo) := { qux : F.(bar) }.
Coercion qux : Baz >-> bar.

Definition f : Foo := {| bar := nat |}.
Canonical Structure f.
Check (fun b : Baz f => b : _.(bar)).

(* Error: Found target class bar instead of bar. *)

(*
This test is sensitive to changes in which let-ins are expanded when checking
for dependencies in constructors.
If the (x := X) is not reduced, Foo1 won't be recognized as a conjunction,
and if the (y := X) is reduced, Foo2 will be recognized as a conjunction.

This tests the behavior of engine/termops.ml : prod_applist_assum,
which is currently specified to reduce exactly the parameters.

If dtauto is changed to reduce lets in constructors before checking dependency,
this test will need to be changed.
*)

Context (P Q : Type).
Inductive Foo1 (X : Type) (x := X) := foo1 : let y := X in P -> Q -> Foo1 x.
Inductive Foo2 (X : Type) (x := X) := foo2 : let y := X in P -> Q -> Foo2 y.

Goal P -> Q -> Foo1 nat.
solve [dtauto].
Qed.

Goal P -> Q -> Foo2 nat.
Fail solve [dtauto].
Abort.

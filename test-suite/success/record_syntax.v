Module A.

Record Foo := { foo : unit; bar : unit }.

Definition foo_ := {|
  foo := tt;
  bar := tt
|}.

Definition foo0 (p : Foo) := match p with {| |} => tt end.
Definition foo1 (p : Foo) := match p with {| foo := f |} => f end.
Definition foo2 (p : Foo) := match p with {| foo := f; |} => f end.
Definition foo3 (p : Foo) := match p with {| foo := f; bar := g |} => (f, g) end.
Definition foo4 (p : Foo) := match p with {| foo := f; bar := g; |} => (f, g) end.

End A.

Module B.

Record Foo := { }.

End B.

Module C.

Record Foo := { foo : unit; bar : unit; }.

Definition foo_ := {|
  foo := tt;
  bar := tt;
|}.

End C.

Module D.

Record Foo := { foo : unit }.
Definition foo_ := {| foo := tt |}.

End D.

Module E.

Record Foo := { foo : unit; }.
Definition foo_ := {| foo := tt; |}.

End E.

Module F.

Record Foo := { foo : nat * nat -> nat -> nat }.

Definition foo_ := {| foo '(x,y) n := x+y+n |}.

End F.

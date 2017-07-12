Set Printing Universes.

Module unidecls.
  Universes a b.
End unidecls.

Universe a.

Constraint a < unidecls.a.

Print Universes.

(** These are different universes *)
Check Type@{a}.
Check Type@{unidecls.a}.

Check Type@{unidecls.b}.

Fail Check Type@{unidecls.c}.

Fail Check Type@{i}.
Universe foo.
Module Foo.
  (** Already declared globaly: but universe names are scoped at the module level  *)
  Universe foo.
  Universe bar.

  Check Type@{Foo.foo}.
  Definition bar := 0.
End Foo.

(** Already declared in the module *)
Universe bar.

(** Accessible outside the module: universe declarations are global *)
Check Type@{bar}.
Check Type@{Foo.bar}.

Check Type@{Foo.foo}.
(** The same *)
Check Type@{foo}.
Check Type@{Top.foo}.

Universe secfoo.
Section Foo'.
  Fail Universe secfoo.
  Universe secfoo2.
  Check Type@{Foo'.secfoo2}.
  Constraint secfoo2 < a.
End Foo'.

Check Type@{secfoo2}.
Fail Check Type@{Foo'.secfoo2}.
Fail Check eq_refl : Type@{secfoo2} = Type@{a}.

(** Below, u and v are global, fixed universes *)
Module Type Arg.
  Universe u.
  Parameter T: Type@{u}.
End Arg.

Module Fn(A : Arg).
  Universes v.

  Check Type@{A.u}.
  Constraint A.u < v.

  Definition foo : Type@{v} := nat.
  Definition bar : Type@{A.u} := nat.

  Fail Definition foo(A : Type@{v}) : Type@{A.u} := A.
End Fn.

Module ArgImpl : Arg.
  Definition T := nat.
End ArgImpl.

Module ArgImpl2 : Arg.
  Definition T := bool.
End ArgImpl2.

(** Two applications of the functor result in the exact same universes *)
Module FnApp := Fn(ArgImpl).

Check Type@{FnApp.v}.
Check FnApp.foo.
Check FnApp.bar.

Check (eq_refl : Type@{ArgImpl.u} = Type@{ArgImpl2.u}).

Module FnApp2 := Fn(ArgImpl).
Check Type@{FnApp2.v}.
Check FnApp2.foo.
Check FnApp2.bar.

Import ArgImpl2.
(** Now u refers to ArgImpl.u and ArgImpl2.u *)
Check FnApp2.bar.

(** It can be shadowed *)
Universe u.

(** This refers to the qualified name *)
Check FnApp2.bar.

Constraint u = ArgImpl.u.
Print Universes.

Set Universe Polymorphism.

Section PS.
  Universe poly.

  Definition id (A : Type@{poly}) (a : A) : A := a.
End PS.
(** The universe is polymorphic and discharged, does not persist *)
Fail Check Type@{poly}.

Print Universes.
Check id nat.
Check id@{Set}.

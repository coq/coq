(* -*- coq-prog-args: ("-noinit" "-top" "unidecls"); -*- *)
Require Import Notations Ltac.
Notation "a -> b" := (forall _:a, b).

Set Printing Universes.

Inductive nat := O | S : nat -> nat.

Module decls.
  Universes a b.
End decls.

Universe a.

Constraint a < decls.a.

Print Universes.

(** These are different universes *)
Check Type@{a}.
Check Type@{decls.a}.

Check Type@{decls.b}.

Fail Check Type@{decls.c}.

Fail Check Type@{i}.
Universe foo.
Module Foo.
  (** Already declared globaly: but universe names are scoped at the module level  *)
  Universe foo.
  Universe bar.

  Check Type@{Foo.foo}.
  Definition bar := O.
End Foo.

(** Already declared in the module *)
Universe bar.

(** Accessible outside the module: universe declarations are global *)
Check Type@{bar}.
Check Type@{Foo.bar}.

Check Type@{Foo.foo}.
(** The same *)
Check Type@{foo}.
Check Type@{unidecls.foo}.

Universe secfoo.
Section Foo'.
  Fail Universe secfoo.
  Universe secfoo2.
  Fail Check Type@{Foo'.secfoo2}.
  Check Type@{secfoo2}.
  Constraint secfoo2 < a.
End Foo'.

Check Type@{secfoo2}.
Fail Check eq_refl : Type@{secfoo2} = Type@{a}.

(** Below, u and v are global, fixed universes *)
Module Type Arg.
  Universe u.
  Parameter T: Type@{u}.
End Arg.

Module Fn(A : Arg).
  Universes v.

  (* univ names are not substitutive *)
  Fail Check Type@{A.u}.
  Check Type@{Arg.u}.
  Constraint Arg.u < v.

  Definition foo : Type@{v} := nat.
  Definition bar : Type@{Arg.u} := nat.

  Definition foo'(A : Type@{v}) : Type@{Arg.u}. Fail exact A. Abort.
End Fn.

Module ArgImpl : Arg.
  Definition T := nat.
End ArgImpl.

Module ArgImpl2 : Arg.
  Definition T := nat.
End ArgImpl2.

(** Two applications of the functor result in the exact same universes *)
Module FnApp := Fn(ArgImpl).

Fail Check Type@{FnApp.v}.
Check Type@{Fn.v}.
Check FnApp.foo.
Check FnApp.bar.

(* "module M : T" does not produce a universe M.u from T.u *)
Fail Check Type@{ArgImpl.u}.

Module FnApp2 := Fn(ArgImpl).
Check FnApp2.foo.
Check FnApp2.bar.

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

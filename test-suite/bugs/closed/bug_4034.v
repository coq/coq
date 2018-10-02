(* This checks compatibility of interpretation scope used for exact
   between 8.4 and 8.5. See discussion at
   https://coq.inria.fr/bugs/show_bug.cgi?id=4034. It is not clear
   what we would like exactly, but certainly, if exact is interpreted
   in a special scope, it should be interpreted consistently so also
   in ltac code. *)

Record Foo := {}.
Bind Scope foo_scope with Foo.
Notation "!" := Build_Foo : foo_scope.
Notation "!" := 1 : core_scope.
Open Scope foo_scope.
Open Scope core_scope.

Goal Foo.
  Fail exact !.
(* ... but maybe will we want it to succeed eventually if we ever
   would be able to make it working the same in

Ltac myexact e := exact e.

Goal Foo.
  myexact !.
Defined.
*)

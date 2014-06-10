Require Import String.

Local Ltac set_strings :=
  let s := match goal with |- context[String ?s1 ?s2] => constr:(String s1 s2) end in
  let H := fresh s in
  set (H := s).

Local Open Scope string_scope.

Goal "asdf" = "bds".
Fail set_strings. (* Error: Ltac variable s is bound to "asdf" which cannot be coerced to
a fresh identifier. *)

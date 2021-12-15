(* These tests are only about a subset of #7068 *)
(* The original issue is still open *)

Inductive foo : let T := Type in T := .
Definition bob1 := Eval vm_compute in foo_rect.
Definition bob2 := Eval native_compute in foo_rect.

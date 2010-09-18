(* We assume the file compiled with -R ../lib lib -R . client *)
(* foo alone should refer to client.foo because -R . client comes last *)

Require Import foo.
Goal a = 1.
reflexivity.
Qed.
Require Import lib.foo.
Goal a = 0.
reflexivity.
Qed.

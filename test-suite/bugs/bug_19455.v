(* -*- coqchk-prog-args: ("-bytecode-compiler" "yes") -*- *)

Require Import PrimString.

Open Scope pstring_scope.

(* coqchk would fail validation of vm data *)
Definition hello := "hello".

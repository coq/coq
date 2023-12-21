(* -*- coq-prog-args: ("-noinit"); -*- *)

Require Import Stdlib.Init.Logic.
Locate Library Stdlib.Init.Logic.

(* Check that Init.Datatypes didn't get exported by the import above *)
Fail Check nat.

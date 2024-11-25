(* -*- coq-prog-args: ("-noinit"); -*- *)

Require Import Corelib.Init.Logic.
Locate Library Corelib.Init.Logic.

(* Check that Init.Datatypes didn't get exported by the import above *)
Fail Check nat.

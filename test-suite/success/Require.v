(* -*- coq-prog-args: ("-noinit"); -*- *)

Require Import Stdlib.Arith.PeanoNat.
Locate Library Stdlib.Arith.PeanoNat.

(* Check that Init didn't get exported by the import above *)
Fail Check nat.

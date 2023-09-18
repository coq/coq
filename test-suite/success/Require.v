(* -*- coq-prog-args: ("-noinit"); -*- *)

Require Import Coq.Arith.PeanoNat.
Locate Library Coq.Arith.PeanoNat.

(* Check that Init didn't get exported by the import above *)
Fail Check nat.

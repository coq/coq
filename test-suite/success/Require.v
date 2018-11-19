(* -*- coq-prog-args: ("-noinit"); -*- *)

Require Import Coq.Arith.Plus.
Require Coq.Arith.Minus.
Locate Library Coq.Arith.Minus.

(* Check that Init didn't get exported by the import above *)
Fail Check nat.

(* -*- coq-prog-args: ("-async-proofs" "off"); -*- *)
(* async proofs off because the output order ends up different with
   and without async *)

(* Example from coq-lsp: we need to test 3 methods where the quickfix
  can come from for the Coq -> Stdlib transition:

  - Coq appearing in require (tested in line 2 of code)
  - Coq appearing in identifiers (tested in Check and Line 1)
  - Coq being looked up via nametab (tested in About)
*)
Require Import Corelib.ssr.ssrbool.
From Corelib Require Import ssreflect ssrbool.

(* Note: this tests the two different lookup modes *)
About Coq.Init.Nat.add.
Check Coq.Init.Nat.add.

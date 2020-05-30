(* Check that inlining does not drop definition needed in signature *)
Require Import Extraction.
Module Type T.
Axiom p : nat.
Axiom n : nat.
End T.
Module M : T.
Definition p := 0.
Definition n := 1.
End M.
Extract Inlined Constant M.n => "1".
Extraction M.

Require Coq.extraction.Extraction.
Require Import FSetList.
Require Import OrderedTypeEx.

Module NatSet := FSetList.Make (Nat_as_OT).
Recursive Extraction NatSet.fold.

Module FSetHide (X : FSetInterface.S).
  Include X.
End FSetHide.

Module NatSet' := FSetHide NatSet.
Recursive Extraction NatSet'.fold.
Extraction TestCompile NatSet'.fold.

(* Extraction "test2141.ml" NatSet'.fold. *)

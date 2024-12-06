(** Check that we avoid an extraction error that came up in PR #14174 in metacoq *)
Require Import Corelib.extraction.ExtrOcamlBasic.
Module A.
  Include Corelib.Init.Specif.
End A.
Recursive Extraction A.
(* Avoding
Error:
The informative inductive type sig2 has a Prop instance
in A.eq_sig2_rec_uncurried (or in its mutual block).
This happens when a sort-polymorphic singleton inductive type
has logical parameters, such as (I,I) : (True * True) : Prop.
The Ocaml extraction cannot handle this situation yet.
Instead, use a sort-monomorphic type such as (True /\ True)
or extract to Haskell.
*)

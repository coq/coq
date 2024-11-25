(* Extraction of primitive projections within a functor were
   incorrectly referencing themselves *)
Module Type Nop. End Nop.
Module Empty. End Empty.
Module M (N : Nop).
  Local Set Primitive Projections.
  Record M_t_NonEmpty elt := { M_m :> list elt }.
  Record M_t_NonEmpty' X Y := { a : X ; b : Y }.
End M.
Module M' := M Empty.
Require Import Corelib.extraction.Extraction.
Require Import Corelib.extraction.ExtrOcamlBasic.
Extraction Language OCaml.
Recursive Extraction M'.
Extraction TestCompile M'.

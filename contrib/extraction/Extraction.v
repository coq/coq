
Declare ML Module "ocaml.cmo" "extraction.cmo".

Grammar vernac vernac : ast :=
  extr_constr [ "Extraction" constrarg($c) "." ] -> [(Extraction $c)].

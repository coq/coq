
(* $Id$ *)

Declare ML Module "refine".

Grammar tactic simple_tactic :=
  tcc [ "Refine" constrarg($c) ] -> [(Tcc $c)].

Syntax tactic level 0:
  tcc [(Tcc $C)] -> ["Refine " $C].
